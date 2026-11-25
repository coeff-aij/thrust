//! The code between an opening marker call and its closing marker call, which the code around it
//! reads through a contract: the region of a `block_contract!` block.

use std::collections::HashSet;

use rustc_middle::mir::{self, BasicBlock, Body, TerminatorKind};

use crate::analyze;

/// How a region of code between two markers is told from the rest of the body: the markers'
/// names for the messages and the blocks that end in them.
pub struct RegionMarkers<'a> {
    /// The opening marker, as a message names it.
    pub open: &'a str,
    /// The closing marker, as a message names it.
    pub close: &'a str,
    /// What to write instead, appended to the message of a path that leaves the function.
    pub leave_hint: &'a str,
    pub is_open: &'a dyn Fn(BasicBlock) -> bool,
    pub is_close: &'a dyn Fn(BasicBlock) -> bool,
}

/// The code between an opening marker call and its closing marker call.
pub struct Region {
    /// The block that ends in the closing marker call.
    pub closing: BasicBlock,
    /// The closing marker's target, the block after the code.
    pub exit: BasicBlock,
    /// The blocks of the code, from `entry` to `closing`.
    pub blocks: HashSet<BasicBlock>,
}

/// The code under the opening marker at `opening`. Stops where a path leaves the function, comes
/// back to the opening, opens another region, or ends in none or several closing markers, and
/// where the code is reached by a path that does not pass the opening.
pub fn region_under<'tcx>(
    ctx: &analyze::Analyzer<'tcx>,
    body: &Body<'tcx>,
    opening: BasicBlock,
    markers: &RegionMarkers<'_>,
) -> Region {
    let terminator = body.basic_blocks[opening].terminator();
    let span = terminator.source_info.span;
    let fatal = |msg: &str| -> ! { ctx.tcx.dcx().span_fatal(span, msg.to_string()) };
    let (open, close) = (markers.open, markers.close);
    let TerminatorKind::Call {
        target: Some(entry),
        ..
    } = terminator.kind
    else {
        unreachable!("a marker call returns");
    };
    let mut blocks = HashSet::new();
    let mut closings = Vec::new();
    let mut stack = vec![entry];
    while let Some(bb) = stack.pop() {
        if !blocks.insert(bb) {
            continue;
        }
        if bb == opening {
            fatal(&format!(
                "a path from {open} comes back to it before a {close}"
            ));
        }
        if (markers.is_close)(bb) {
            closings.push(bb);
            continue;
        }
        if (markers.is_open)(bb) {
            fatal("a block contract inside another block contract is not supported");
        }
        let terminator = body.basic_blocks[bb].terminator();
        if matches!(
            terminator.kind,
            TerminatorKind::Return | TerminatorKind::Yield { .. } | TerminatorKind::CoroutineDrop
        ) {
            fatal(&format!(
                "a path from {open} leaves the function before a {close}{}",
                markers.leave_hint
            ));
        }
        stack.extend(
            terminator
                .successors()
                .filter(|succ| !body.basic_blocks[*succ].is_cleanup),
        );
    }
    let closing = match closings.as_slice() {
        [closing] => *closing,
        [] => fatal(&format!("no {close} follows {open} on a path that returns")),
        _ => fatal(&format!("several {close} close one {open}")),
    };
    let TerminatorKind::Call {
        target: Some(exit), ..
    } = body.basic_blocks[closing].terminator().kind
    else {
        unreachable!("a marker call returns");
    };
    if blocks.contains(&exit) {
        fatal(&format!(
            "the code after {close} is also under its contract"
        ));
    }
    if entered_from_outside(body, &blocks, entry) {
        fatal(&format!(
            "the code under {open} is also reached by a path that does not pass it"
        ));
    }
    Region {
        closing,
        exit,
        blocks,
    }
}

/// Whether a block of the region, other than its first, has a predecessor outside it: a path that
/// reaches the code without the opening marker, such as the other arm of an `if` whose one arm
/// holds the marker. The analysis reads the code only from the marker, so such a path would not
/// reach the code after the closing marker's contract. The code must be entered only through the
/// opening marker, as a statement contract in ACSL or Why3's abstract block, which are
/// single-entry by their syntax. A predecessor no path from the start reaches is no way in.
fn entered_from_outside(body: &Body<'_>, blocks: &HashSet<BasicBlock>, entry: BasicBlock) -> bool {
    let predecessors = body.basic_blocks.predecessors();
    let reachable = mir::traversal::reachable_as_bitset(body);
    let way_in = |pred: &BasicBlock| {
        !blocks.contains(pred) && !body.basic_blocks[*pred].is_cleanup && reachable.contains(*pred)
    };
    blocks
        .iter()
        .filter(|&&bb| bb != entry)
        .any(|&bb| predecessors[bb].iter().any(way_in))
}
