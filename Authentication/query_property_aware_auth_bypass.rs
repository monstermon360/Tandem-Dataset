// tests/query_property_aware_auth_bypass.rs
//
// Standalone fork of auth_bypass_findings's provenance logic, extended to
// traverse Store/Load edges (property write/read) in addition to
// DirectFlow. This file does not modify auth.rs -- it's a fully separate
// copy of the relevant private functions, adapted here, so the original
// stays untouched. See auth_provenance_fix.patch for the equivalent
// one-line-of-reasoning change if this ever gets folded back into auth.rs
// directly.
//
// Everything below down to `pa_auth_bypass_findings` is adapted from
// tandem-queries/src/auth.rs (Query A: dominance-based auth-bypass). The
// `pa_` prefix ("property-aware") avoids any naming collision. The single
// substantive change from the original is inside `pa_provenance_verdict`:
// the reverse-edge filter additionally matches Store/Load edges, not just
// DirectFlow -- see the comment at that line for the full reasoning.
//
// AuthBypassFinding itself is not redefined -- it's already public via
// tandem_queries, so this fork returns the exact same type the original
// auth_bypass_findings does, making the two directly comparable.

use fxhash::FxHashSet;
use oxc_cfg::BlockNodeId;

use tandem::analysis::graph::dataflow_graph::{
    DataflowEdgeKind, DataflowNode, DataflowNodeId, LocalDataflowGraph, NodeOperation,
    NodeOperationKind,
};
use tandem::environment::storage::abstract_value::AbstractValue;
use tandem::environment::types::{PrimitiveValue, Type};
use tandem::environment::GlobalNodeId;
use tandem::environment::MemoKey;
use tandem::Tandem;

use tandem_queries::AuthBypassFinding;

const MAX_PROVENANCE_DEPTH: u32 = 8;

// --- Copied verbatim from auth.rs (value_could_be_truthy) ---
fn pa_value_could_be_truthy(value: &AbstractValue) -> bool {
    if value.get_values().is_empty() {
        return true;
    }
    value.get_values().iter().any(|v| match v {
        Type::Primitive(PrimitiveValue::Boolean(false)) => false,
        Type::Primitive(PrimitiveValue::Number(n)) if **n == 0.0 => false,
        Type::Primitive(PrimitiveValue::Null) => false,
        Type::Primitive(PrimitiveValue::Undefined) => false,
        Type::Primitive(PrimitiveValue::String(_)) => true,
        _ => true,
    })
}

/// Entry point. Same signature and semantics as tandem_queries::auth_bypass_findings,
/// except the provenance walk below additionally accepts property-based guards.
pub fn pa_auth_bypass_findings(
    tandem: &Tandem,
    is_sink: impl Fn(&DataflowNode) -> bool,
    auth_names: &[&str],
) -> Vec<AuthBypassFinding> {
    let auth_fn_ids: FxHashSet<GlobalNodeId> = {
        let env = tandem.get_global_env();
        env.iter_function_metadata()
            .filter_map(|(gid, md)| {
                md.name
                    .as_deref()
                    .and_then(|n| auth_names.contains(&n).then(|| gid.clone()))
            })
            .collect()
    };

    let mut findings = Vec::new();

    let memo_keys: Vec<MemoKey> = {
        let env = tandem.get_global_env();
        env.memo_table()
            .full_entries_with_summaries()
            .filter_map(|(fn_id, shape, _)| {
                if shape.args().len() >= 2 && shape.args()[1..].iter().all(|a| a.is_bottom()) {
                    return None;
                }
                Some(MemoKey::new(fn_id.clone(), shape.clone()))
            })
            .collect()
    };

    for memo_key in memo_keys {
        let Some(cfg) = tandem.cfg_in_memo(&memo_key) else {
            continue;
        };

        let dfg = {
            let env = tandem.get_global_env();
            let Some(summary) = env.memo_lookup(
                memo_key.function_node_id.node_id,
                memo_key.function_node_id.file_path.as_ref(),
                memo_key.arg_shape.args().to_vec(),
                memo_key.arg_shape.is_constructor,
            ) else {
                continue;
            };
            let Some(dfg) = summary.dataflow_graph.as_ref() else {
                continue;
            };
            dfg.clone()
        };

        for node in dfg.all_nodes() {
            if !is_sink(node) {
                continue;
            }
            let sink_pp = node.id.location.clone();
            let Some(sink_block) = cfg.block_containing(&sink_pp) else {
                continue;
            };

            let guarded = pa_block_is_auth_guarded(&cfg, &dfg, sink_block, &auth_fn_ids, 0);

            if !guarded {
                let sink_name = match &node.operation {
                    NodeOperation::Call { function_name, .. } => function_name.clone(),
                    _ => None,
                };
                findings.push(AuthBypassFinding {
                    sink_pp,
                    sink_name,
                    memo_key: memo_key.clone(),
                });
            }
        }
    }

    findings
}

fn pa_condition_contains_auth_call_at_polarity(
    cfg: &tandem::analysis::cfg::CfgQueryEngine,
    dfg: &LocalDataflowGraph,
    cond_nid: oxc_syntax::node::NodeId,
    required_polarity: bool,
    auth_fn_ids: &FxHashSet<GlobalNodeId>,
    depth: u32,
) -> bool {
    cfg.condition_proves_at(cond_nid, required_polarity, &|nid, target| {
        if !target {
            return false;
        }
        for node in dfg.all_nodes() {
            if node.id.location.node_id != nid {
                continue;
            }
            if let NodeOperation::Call { callees, .. } = &node.operation {
                if callees
                    .iter()
                    .any(|c| auth_fn_ids.contains(&c.function_node_id))
                {
                    return true;
                }
            }
            if matches!(
                node.id.kind,
                NodeOperationKind::Identifier | NodeOperationKind::PropertyRead
            ) {
                let ok = pa_identifier_provenance_is_auth(
                    cfg, dfg, &node.id, target, auth_fn_ids, depth,
                );
                if ok {
                    return true;
                }
            }
        }
        false
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PaProvenanceVerdict {
    Accept,
    SkipIncompatible,
    Reject,
}

fn pa_identifier_provenance_is_auth(
    cfg: &tandem::analysis::cfg::CfgQueryEngine,
    dfg: &LocalDataflowGraph,
    start: &DataflowNodeId,
    required_polarity: bool,
    auth_fn_ids: &FxHashSet<GlobalNodeId>,
    depth: u32,
) -> bool {
    let _ = required_polarity;
    let mut visited: FxHashSet<DataflowNodeId> = FxHashSet::default();
    let verdict = pa_provenance_verdict(cfg, dfg, start, auth_fn_ids, &mut visited, depth);
    matches!(verdict, PaProvenanceVerdict::Accept)
}

/// The two substantive changes from auth.rs:
/// 1. Below, in `pa_provenance_verdict`: the reverse-edge filter additionally
///    matches Store edges (property write), not just DirectFlow. This is
///    what lets the walk cross from a PropertyWrite node back to the Call
///    that produced the written value (e.g. `state.authorized =
///    authenticate(req)` -- PropertyWrite's only incoming edge to the Call
///    is a Store edge). Load edges are deliberately NOT included: empirically
///    (see query_dump_property_guard_graph.rs output), a PropertyRead's
///    incoming Load edges point to structural/identity nodes -- the base
///    identifier being dereferenced and the object's allocation site -- not
///    to value provenance. DirectFlow already carries the actual "last
///    write" link (PropertyWrite --DirectFlow--> PropertyRead), so Store is
///    the only edge kind actually missing.
/// 2. In `pa_condition_contains_auth_call_at_polarity`: the leaf predicate's
///    kind check now also accepts NodeOperationKind::PropertyRead, not just
///    Identifier. This turned out to be the primary reason the original
///    provenance walk never fired at all for `if (state.authorized)`-style
///    conditions -- the condition node's kind is PropertyRead, so the
///    Identifier-only check silently skipped it before the walk could even
///    begin, regardless of what provenance_verdict's edge traversal allowed.
fn pa_provenance_verdict(
    cfg: &tandem::analysis::cfg::CfgQueryEngine,
    dfg: &LocalDataflowGraph,
    nid: &DataflowNodeId,
    auth_fn_ids: &FxHashSet<GlobalNodeId>,
    visited: &mut FxHashSet<DataflowNodeId>,
    depth: u32,
) -> PaProvenanceVerdict {
    if !visited.insert(nid.clone()) {
        return PaProvenanceVerdict::SkipIncompatible;
    }

    let node = dfg.get_node(nid);

    if let Some(n) = node {
        if let NodeOperation::Call { callees, .. } = &n.operation {
            let is_auth = callees
                .iter()
                .any(|c| auth_fn_ids.contains(&c.function_node_id));
            return if is_auth {
                PaProvenanceVerdict::Accept
            } else {
                PaProvenanceVerdict::Reject
            };
        }
    }

    if let Some(n) = node {
        if !pa_value_could_be_truthy(&n.abstract_value) {
            return PaProvenanceVerdict::SkipIncompatible;
        }
    }

    let mut saw_pred = false;
    let mut saw_accept = false;
    let mut saw_reject = false;
    for &idx in dfg.get_reverse_edges(nid) {
        let edge = dfg.get_edge(idx);
        // <-- the actual fix: widened from `DataflowEdgeKind::DirectFlow` only.
        let is_traversable = matches!(
            edge.kind,
            DataflowEdgeKind::DirectFlow
                | DataflowEdgeKind::Store { .. }
        );
        if is_traversable {
            saw_pred = true;
            match pa_provenance_verdict(cfg, dfg, &edge.source, auth_fn_ids, visited, depth) {
                PaProvenanceVerdict::Accept => saw_accept = true,
                PaProvenanceVerdict::Reject => saw_reject = true,
                PaProvenanceVerdict::SkipIncompatible => {}
            }
        }
    }

    if saw_pred {
        if saw_reject {
            return PaProvenanceVerdict::Reject;
        }
        if saw_accept {
            return PaProvenanceVerdict::Accept;
        }
        return PaProvenanceVerdict::SkipIncompatible;
    }

    let Some(block) = cfg.block_containing(&nid.location) else {
        return PaProvenanceVerdict::Reject;
    };
    if pa_block_is_auth_guarded(cfg, dfg, block, auth_fn_ids, depth + 1) {
        PaProvenanceVerdict::Accept
    } else {
        PaProvenanceVerdict::Reject
    }
}

fn pa_block_is_auth_guarded(
    cfg: &tandem::analysis::cfg::CfgQueryEngine,
    dfg: &LocalDataflowGraph,
    target_block: BlockNodeId,
    auth_fn_ids: &FxHashSet<GlobalNodeId>,
    depth: u32,
) -> bool {
    if depth > MAX_PROVENANCE_DEPTH {
        return false;
    }
    for dom_block in cfg.dominators_of(target_block) {
        if dom_block == target_block {
            continue;
        }
        let Some(cond_nid) = cfg.condition_of_block(dom_block) else {
            continue;
        };
        let Some(required_polarity) = cfg.sink_branch_polarity(dom_block, target_block) else {
            continue;
        };
        if pa_condition_contains_auth_call_at_polarity(
            cfg,
            dfg,
            cond_nid,
            required_polarity,
            auth_fn_ids,
            depth,
        ) {
            return true;
        }
    }
    false
}

// ============================================================================
// Tests: run the property-aware fork against every probe file we already
// built and validated against the original auth_bypass_findings, checking
// that it agrees on everything except the property-guard false positive,
// which it should now correctly clear.
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tandem_queries::call_named;

    const PROPERTY_GUARD_PROBE: &str =
        "/mnt/c/Users/monst/OneDrive/Documents/Program Analysis/auth_bypass_findings/property_guard_probe.js";
    const AUTH_GAP_PROBE_2: &str =
        "/mnt/c/Users/monst/OneDrive/Documents/Program Analysis/auth_bypass_findings/auth_gap_probe_2.js";

    #[test]
    fn property_guard_is_now_correctly_cleared() {
        let tandem = Tandem::from_script(PROPERTY_GUARD_PROBE)
            .expect("probe should parse and reach fixpoint");
        let findings = pa_auth_bypass_findings(&tandem, call_named("save"), &["authenticate"]);

        for f in &findings {
            println!("finding: {:?}", f.sink_pp);
        }

        // Both propertyGuardController and variableGuardController are
        //  guarded -- expect zero findings from this file now.
        assert!(
            findings.is_empty(),
            "expected no findings on property_guard_probe.js after the fix; \
             got {} -- the Store/Load widening may not be working as intended",
            findings.len()
        );
    }

    #[test]
    fn property_bypass_is_still_correctly_flagged() {
        let tandem = Tandem::from_script(AUTH_GAP_PROBE_2)
            .expect("probe should parse and reach fixpoint");
        let findings = pa_auth_bypass_findings(&tandem, call_named("save"), &["authenticate"]);

        let functions_flagged: Vec<String> = {
            let env = tandem.get_global_env();
            findings
                .iter()
                .map(|f| {
                    if env.has_function_metadata(
                        f.memo_key.function_node_id.node_id,
                        &f.memo_key.function_node_id.file_path,
                    ) {
                        env.get_function_metadata(
                            f.memo_key.function_node_id.node_id,
                            &f.memo_key.function_node_id.file_path,
                        )
                        .name
                        .clone()
                        .unwrap_or_else(|| "<anon>".to_string())
                    } else {
                        "<top-level>".to_string()
                    }
                })
                .collect()
        };
        println!("flagged functions: {:?}", functions_flagged);

        // This is the critical regression check: propertyBypassController
        // has a genuine bypass (an unrelated header branch clobbers the
        // property to `true`) and must still be caught. If the widened
        // traversal accidentally started accepting this too, the fix went
        // too far and is now hiding a real vulnerability.
        assert!(
            functions_flagged
                .iter()
                .any(|f| f == "propertyBypassController"),
            "regression: propertyBypassController should still be flagged -- \
             it has a genuine property-based bypass, not a false positive"
        );

        // propertyGuardController (control case, genuinely guarded) should
        // not be in this file's findings either.
        assert!(
            !functions_flagged
                .iter()
                .any(|f| f == "propertyGuardController"),
            "propertyGuardController should not be flagged -- it's genuinely guarded"
        );
    }

    const BENEFITS_FILE: &str = "/mnt/c/Users/monst/OneDrive/Documents/Program Analysis/auth_bypass_findings/benefits.js";

    #[test]
    fn benefits_js_exploration() {
        let opts = tandem::AnalysisOptions {
            drive_exports: true,
            ..Default::default()
        };
        let tandem = Tandem::from_script_with_options(BENEFITS_FILE, opts)
            .expect("file should parse and reach fixpoint");

        let findings = pa_auth_bypass_findings(&tandem, call_named("updateBenefits"), &["isAdmin"]);

        println!("findings: {}", findings.len());
        for f in &findings {
            println!("  {:?}", f.sink_pp);
        }
    }
}
