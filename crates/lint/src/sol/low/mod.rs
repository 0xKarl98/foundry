use crate::sol::{EarlyLintPass, LateLintPass, SolLint};

mod block_timestamp;
use block_timestamp::BLOCK_TIMESTAMP;

mod missing_zero_check;
use missing_zero_check::MISSING_ZERO_CHECK;

mod missing_events_access_control;
use missing_events_access_control::MISSING_EVENTS_ACCESS_CONTROL;

register_lints!(
    (BlockTimestamp, early, (BLOCK_TIMESTAMP)),
    (MissingEventsAccessControl, late, (MISSING_EVENTS_ACCESS_CONTROL)),
    (MissingZeroCheck, late, (MISSING_ZERO_CHECK)),
);
