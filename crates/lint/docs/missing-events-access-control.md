# Missing events access control

**Severity**: `Low`
**ID**: `missing-events-access-control`

Flags protected functions that change `address` state used by access-control modifiers without
emitting an event.

## What it does

Detects externally callable, state-mutating functions that are protected by a modifier, do not emit
any event, and write to an `address` state variable that is read by an access-control modifier.

## Why is this bad?

Access-control state changes, such as ownership transfers, are important operational events.
Without an emitted event, off-chain monitors, indexers, and auditors have to reconstruct the change
from storage writes instead of observing an explicit signal.

## Example

### Bad

```solidity
function transferOwnership(address newOwner) external onlyOwner {
    owner = newOwner;
}
```

### Good

```solidity
event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

function transferOwnership(address newOwner) external onlyOwner {
    emit OwnershipTransferred(owner, newOwner);
    owner = newOwner;
}
```
