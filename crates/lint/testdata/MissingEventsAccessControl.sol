//@compile-flags: --only-lint missing-events-access-control

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.18;

contract BaseOwner {
    address public inheritedOwner;

    // Inherited access-control authorities should be treated the same as local authorities.
    modifier onlyInheritedOwner() {
        require(msg.sender == inheritedOwner, "not inherited owner");
        _;
    }
}

contract MissingEventsAccessControl is BaseOwner {
    address public owner;
    address public admin;
    address public pendingOwner;
    address public treasury;
    uint256 public threshold;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    // Canonical owner gate used to mark owner as an access-control authority.
    modifier onlyOwner() {
        require(msg.sender == owner, "not owner");
        _;
    }

    // A second authority verifies that the lint tracks more than the conventional owner name.
    modifier onlyAdmin() {
        require(msg.sender == admin, "not admin");
        _;
    }

    // Writes in a modifier should not warn unless the modifier invocation itself is protected.
    modifier writesPendingOwner(address nextOwner) {
        pendingOwner = nextOwner;
        _;
    }

    // Protected state writes that execute from a modifier body should still be reported.
    modifier writesOwner(address nextOwner) {
        owner = nextOwner; //~WARN: access control state change should emit an event
        _;
    }

    // Non-sender sanity checks must not make treasury an access-control authority.
    modifier checkTreasury() {
        require(treasury != address(0), "treasury unset");
        _;
    }

    // Parameterized access-control modifiers map their argument to the authority at each call site.
    modifier only(address who) {
        require(msg.sender == who, "not authorized");
        _;
    }

    // An event emitted by an invoked modifier satisfies the missing-event requirement.
    modifier emitsOwnershipChange(address newOwner) {
        emit OwnershipTransferred(owner, newOwner);
        _;
    }

    // Modifier names alone are not access control; the body must actually gate on msg.sender.
    modifier nonAccessControl() {
        _;
    }

    constructor(address initialOwner) {
        owner = initialOwner;
    }

    // SHOULD WARN:

    // Direct protected owner update without an event should warn.
    function transferOwnership(address newOwner) external onlyOwner {
        owner = newOwner; //~WARN: access control state change should emit an event
    }

    // Taint should flow through a local alias initialized from an entry parameter.
    function transferOwnershipViaAlias(address newOwner) external onlyOwner {
        address nextOwner = newOwner;
        owner = nextOwner; //~WARN: access control state change should emit an event
    }

    // Inherited authorities are still access-control state for the derived contract function.
    function transferInheritedOwnership(address newOwner) external onlyInheritedOwner {
        inheritedOwner = newOwner; //~WARN: access control state change should emit an event
    }

    // Updating another authority under owner control should also emit an event.
    function transferAdmin(address newAdmin) external onlyOwner {
        admin = newAdmin; //~WARN: access control state change should emit an event
    }

    // Inline require guards should be recognized even without an access-control modifier.
    function transferAdminInline(address newAdmin) external {
        require(msg.sender == owner, "not owner");
        admin = newAdmin; //~WARN: access control state change should emit an event
    }

    // Generic parameterized guards should mark the invocation argument as the authority.
    function transferOwnershipGeneric(address newOwner) external only(owner) {
        owner = newOwner; //~WARN: access control state change should emit an event
    }

    // The externally callable function is empty, but the invoked modifier writes owner.
    function transferOwnershipInModifier(address newOwner) external onlyOwner writesOwner(newOwner) {}

    // Constant authority updates still change access control and should emit an event.
    function setOwnerViaClearedAlias(address newOwner) external onlyOwner {
        address nextOwner = newOwner;
        nextOwner = address(0x1234);
        owner = nextOwner; //~WARN: access control state change should emit an event
    }

    // SHOULD NOT WARN:

    // The protected authority update already emits an event in the function body.
    function transferOwnershipWithEvent(address newOwner) external onlyOwner {
        emit OwnershipTransferred(owner, newOwner);
        owner = newOwner;
    }

    // Treasury is not used as an access-control authority, so this state update is out of scope.
    function setTreasury(address newTreasury) external onlyOwner {
        treasury = newTreasury;
    }

    // A non-sender sanity modifier should not turn treasury into an authority.
    function setTreasuryWithSanityModifier(address newTreasury) external onlyOwner checkTreasury {
        treasury = newTreasury;
    }

    // An event emitted from a modifier covers the authority update in the function body.
    function transferOwnershipWithModifierEvent(address newOwner)
        external
        onlyOwner
        emitsOwnershipChange(newOwner)
    {
        owner = newOwner;
    }

    // The writing modifier is not protected, and pendingOwner is not an access-control authority.
    function setPendingOwner(address newPendingOwner) external writesPendingOwner(newPendingOwner) {
        pendingOwner = newPendingOwner;
    }

    // A modifier with no sender gate should not make this function protected.
    function setAdminWithNonAccessModifier(address newAdmin) external nonAccessControl {
        admin = newAdmin;
    }

    // Missing access control is a separate lint; this rule only checks protected authority updates.
    function unprotectedTransferOwnership(address newOwner) external {
        owner = newOwner;
    }

    // A sender branch is not a guard unless the unauthorized path exits before the write.
    function unprotectedSenderBranch(address newOwner) external {
        if (msg.sender == owner) {
            treasury = msg.sender;
        }
        owner = newOwner;
    }

    // Non-address state is not tracked as an access-control authority.
    function setThreshold(uint256 newThreshold) external onlyOwner {
        threshold = newThreshold;
    }
}

contract InlineOnlyAccessControl {
    address public owner;

    // Inline msg.sender gates should collect owner as the authority without any modifier help.
    function transferOwnership(address newOwner) external {
        require(msg.sender == owner, "not owner");
        owner = newOwner; //~WARN: access control state change should emit an event
    }
}

contract ParameterizedAccessControl {
    address public owner;
    address public admin;

    modifier only(address who) {
        require(msg.sender == who, "not authorized");
        _;
    }

    // This invocation teaches the lint that admin can be the authority for the generic modifier.
    function adminAction() external only(admin) {}

    // The current invocation is only(owner), but admin is known as an authority from another call.
    function setAdmin(address newAdmin) external only(owner) {
        admin = newAdmin; //~WARN: access control state change should emit an event
    }
}

contract NonAccessSenderRequire {
    address public owner;

    modifier onlyOwner() {
        require(msg.sender == owner, "not owner");
        _;
    }

    // Mentioning msg.sender is not enough; the check must compare against an authority.
    function unprotectedSetOwner(address newOwner) external {
        require(msg.sender != address(0), "zero sender");
        owner = newOwner;
    }
}

contract NegativeSenderAuthorityRequire {
    address public owner;

    // Negative sender checks do not protect the authority; they exclude it.
    function setOwnerWhenNotOwner(address newOwner) external {
        require(msg.sender != owner, "owner not allowed");
        owner = newOwner;
    }
}

contract UserChosenModifierAuthority {
    address public owner;

    modifier only(address who) {
        require(msg.sender == who, "not authorized");
        _;
    }

    function ownerAction() external only(owner) {}

    // The caller controls `who`, so this invocation is not an authority-backed guard.
    function setOwner(address who, address newOwner) external only(who) {
        owner = newOwner;
    }
}

contract ConstantAuthorityUpdate {
    address public owner;

    modifier onlyOwner() {
        require(msg.sender == owner, "not owner");
        _;
    }

    // Overwriting a parameter with a constant still changes the owner authority.
    function setOwnerViaConstantParam(address newOwner) external onlyOwner {
        newOwner = address(0x1234);
        owner = newOwner; //~WARN: access control state change should emit an event
    }
}

contract MisleadingModifierName {
    address public owner;
    bool public flag = true;

    modifier onlyOwner() {
        // The misleading modifier name is ignored because the body has no msg.sender authority gate.
        require(flag, "paused");
        _;
    }

    // This stays quiet even though the modifier is named onlyOwner.
    function setOwner(address newOwner) external onlyOwner {
        owner = newOwner;
    }
}
