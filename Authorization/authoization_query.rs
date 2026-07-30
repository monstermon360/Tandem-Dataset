// tests/query_idor.rs
//
// Skeleton for the IDOR detection query. Structurally simpler than
// query_property_aware_auth_bypass.rs: no recursive provenance-verdict
// combining needed, since we're checking "does this trace to a specific
// property path" (a direct backward walk), not "does this trace to a
// named auth function" (which needed accept/reject/skip combining across
// multiple incoming edges).

use fxhash::FxHashSet;
use tandem::analysis::graph::dataflow_graph::{
    DataflowEdgeKind, DataflowNode, DataflowNodeId, LocalDataflowGraph, NodeOperation,
    NodeOperationKind,
};
use tandem::environment::MemoKey;
use tandem::Tandem;

use tandem_queries::AuthBypassFinding;

const MAX_DEPTH: u32 = 8;

/// Walk backward from `start` through DirectFlow/Load edges, collecting
/// property names in the order encountered, until reaching a Parameter
/// node. Returns None if the walk doesn't terminate cleanly at a
/// Parameter (e.g. hits a dead end, or exceeds MAX_DEPTH).
///
/// TODO: implement using dfg.get_reverse_edges(nid) / dfg.get_edge(idx),
/// same pattern as pa_provenance_verdict's edge loop -- but no branching
/// combine logic needed here, just follow the single relevant predecessor
/// at each step (DirectFlow always; Load when the property name matters).
fn trace_property_path(
    dfg: &LocalDataflowGraph,
    start: &DataflowNodeId,
) -> Option<Vec<String>> {
    let mut path: Vec<String> = Vec::new();
    let mut current = start.clone();
    let mut visited: FxHashSet<DataflowNodeId> = FxHashSet::default();
    let mut depth = 0;

    loop {
        if depth > MAX_DEPTH {
            return None;
        }
        depth += 1;

        if !visited.insert(current.clone()) {
            return None; // cycle guard
        }

        let node = dfg.get_node(&current)?;
        if matches!(node.id.kind, NodeOperationKind::Parameter) {
            path.reverse(); // collected leaf-to-root; caller wants root-to-leaf
            return Some(path);
        }

        // Take the first DirectFlow or Load predecessor -- unlike the
        // auth-bypass provenance walk, we're tracing a single concrete
        // value's origin, not combining multiple possible sources, so one
        // matching edge per step is expected.
        let mut next: Option<DataflowNodeId> = None;
        for &idx in dfg.get_reverse_edges(&current) {
            let edge = dfg.get_edge(idx);
            match &edge.kind {
                DataflowEdgeKind::DirectFlow => {
                    next = Some(edge.source.clone());
                    break;
                }
                DataflowEdgeKind::Load { property } => {
                    path.push(property.clone());
                    next = Some(edge.source.clone());
                    break;
                }
                _ => {}
            }
        }

        current = next?;
    }
}

/// Given a BinaryOp condition node's id, check whether it's a genuine
/// ownership comparison: one operand traces to a "params"-rooted path,
/// the other to a "session"-rooted path, with matching final property
/// name (e.g. both end in "userId").
///
/// TODO: find the node at cond_nid in dfg, confirm NodeOperationKind::BinaryOp,
/// find its two incoming Derivation edges (dfg.get_reverse_edges +
/// filter on DataflowEdgeKind::Derivation), call trace_property_path on
/// each edge's source, then check the two resulting paths.
fn condition_is_ownership_check(
    dfg: &LocalDataflowGraph,
    cond_nid: oxc_syntax::node::NodeId,
) -> bool {
    let Some(binop_node) = dfg.all_nodes().find(|n| {
        n.id.location.node_id == cond_nid && matches!(n.id.kind, NodeOperationKind::BinaryOp)
    }) else {
        return false;
    };
    let binop_id = binop_node.id.clone();

    let mut operand_paths: Vec<Vec<String>> = Vec::new();
    for &idx in dfg.get_reverse_edges(&binop_id) {
        let edge = dfg.get_edge(idx);
        if matches!(edge.kind, DataflowEdgeKind::Derivation) {
            if let Some(path) = trace_property_path(dfg, &edge.source) {
                operand_paths.push(path);
            }
        }
    }

    // A genuine comparison has exactly two operands. Fewer/more means this
    // isn't the shape we're looking for (or trace_property_path failed on
    // one side, which we treat conservatively as "not recognized" rather
    // than guessing).
    if operand_paths.len() != 2 {
        return false;
    }

    let (a, b) = (&operand_paths[0], &operand_paths[1]);
    let a_root = a.first().map(String::as_str);
    let b_root = b.first().map(String::as_str);

    let is_params_session_pair = (a_root == Some("params") && b_root == Some("session"))
        || (a_root == Some("session") && b_root == Some("params"));

    // Also require the final property name to match (e.g. both "userId")
    // -- catches wrongComparisonController's self-comparison trap too,
    // since that resolves to the SAME path on both sides (same root, not
    // a params/session pair), so it already fails the check above; this
    // guards the case where roots differ but the compared fields don't
    // (e.g. accidentally comparing req.params.userId to req.session.role).
    is_params_session_pair && a.last() == b.last()
}

fn block_is_ownership_guarded(
    cfg: &tandem::analysis::cfg::CfgQueryEngine,
    dfg: &LocalDataflowGraph,
    target_block: oxc_cfg::BlockNodeId,
) -> bool {
    for dom_block in cfg.dominators_of(target_block) {
        if dom_block == target_block {
            continue;
        }
        let Some(cond_nid) = cfg.condition_of_block(dom_block) else {
            continue;
        };
        // NOTE: unlike pa_block_is_auth_guarded, we don't need
        // sink_branch_polarity here yet -- condition_is_ownership_check
        // doesn't currently look at which branch we're in. Worth
        // revisiting once this compiles: does an inverted comparison
        // (e.g. `!==`) need separate handling, similar to how
        // invertedConditionController needed polarity-awareness in the
        // auth-bypass case?
        if condition_is_ownership_check(dfg, cond_nid) {
            return true;
        }
    }
    false
}

pub fn idor_findings(
    tandem: &Tandem,
    is_sink: impl Fn(&DataflowNode) -> bool,
) -> Vec<AuthBypassFinding> {
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

            let guarded = block_is_ownership_guarded(&cfg, &dfg, sink_block);

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

#[cfg(test)]
mod tests {
    use super::*;
    use tandem_queries::call_named;

    const IDOR_PROBE: &str =
        "/mnt/c/Users/monst/OneDrive/Documents/Program Analysis/auth_bypass_findings/idor_probe.js";

    const ALLOCATIONS_FILE: &str =
    "/mnt/c/Users/monst/OneDrive/Documents/Program Analysis/auth_bypass_findings/allocations.js";


    #[test]
    fn idor_probe_results() {
        let tandem = Tandem::from_script(IDOR_PROBE)
            .expect("probe should parse and reach fixpoint");
        let findings = idor_findings(&tandem, call_named("getResource"));

        let env = tandem.get_global_env();
        for f in &findings {
            let name = if env.has_function_metadata(
                f.memo_key.function_node_id.node_id,
                &f.memo_key.function_node_id.file_path,
            ) {
                env.get_function_metadata(
                    f.memo_key.function_node_id.node_id,
                    &f.memo_key.function_node_id.file_path,
                )
                .name
                .clone()
            } else {
                None
            };
            println!("flagged: {:?}", name);
        }

        // Fill in once trace_property_path / condition_is_ownership_check
        // are implemented -- per the scorecard from earlier:
        //   vulnerableIdorController, comparisonIgnoredController,
        //   wrongComparisonController -> should be flagged
        //   safeOwnResourceController, adminOverrideController -> should not
    }

    #[test]
    fn allocations_js_exploration() {
        let opts = tandem::AnalysisOptions {
            drive_exports: true,
            ..Default::default()
        };
        let tandem = Tandem::from_script_with_options(ALLOCATIONS_FILE, opts)
            .expect("file should parse and reach fixpoint");

        let findings = idor_findings(&tandem, call_named("getByUserIdAndThreshold"));

        let env = tandem.get_global_env();
        for f in &findings {
            let name = if env.has_function_metadata(
                f.memo_key.function_node_id.node_id,
                &f.memo_key.function_node_id.file_path,
            ) {
                env.get_function_metadata(
                    f.memo_key.function_node_id.node_id,
                    &f.memo_key.function_node_id.file_path,
                )
                .name
                .clone()
            } else {
                None
            };
            println!("flagged: {:?}", name);
        }

        println!("total findings: {}", findings.len());
    }
}
