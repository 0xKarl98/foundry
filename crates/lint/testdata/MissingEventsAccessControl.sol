//@compile-flags: --only-lint missing-events-access-control

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.18;

contract BaseOwner {
    address public inheritedOwner;

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

    modifier onlyOwner() {
        require(msg.sender == owner, "not owner");
        _;
    }

    modifier onlyAdmin() {
        require(msg.sender == admin, "not admin");
        _;
    }

    modifier writesPendingOwner(address nextOwner) {
        pendingOwner = nextOwner;
        _;
    }

    modifier checkTreasury() {
        require(treasury != address(0), "treasury unset");
        _;
    }

    modifier only(address who) {
        require(msg.sender == who, "not authorized");
        _;
    }

    modifier emitsOwnershipChange(address newOwner) {
        emit OwnershipTransferred(owner, newOwner);
        _;
    }

    modifier nonAccessControl() {
        _;
    }

    constructor(address initialOwner) {
        owner = initialOwner;
    }

    // SHOULD WARN:

    function transferOwnership(address newOwner) external onlyOwner {
        owner = newOwner; //~WARN: access control state change should emit an event
    }

    function transferOwnershipViaAlias(address newOwner) external onlyOwner {
        address nextOwner = newOwner;
        owner = nextOwner; //~WARN: access control state change should emit an event
    }

    function transferInheritedOwnership(address newOwner) external onlyInheritedOwner {
        inheritedOwner = newOwner; //~WARN: access control state change should emit an event
    }

    function transferAdmin(address newAdmin) external onlyOwner {
        admin = newAdmin; //~WARN: access control state change should emit an event
    }

    function transferAdminInline(address newAdmin) external {
        require(msg.sender == owner, "not owner");
        admin = newAdmin; //~WARN: access control state change should emit an event
    }

    function transferOwnershipGeneric(address newOwner) external only(owner) {
        owner = newOwner; //~WARN: access control state change should emit an event
    }

    // SHOULD NOT WARN:

    function transferOwnershipWithEvent(address newOwner) external onlyOwner {
        emit OwnershipTransferred(owner, newOwner);
        owner = newOwner;
    }

    function setTreasury(address newTreasury) external onlyOwner {
        treasury = newTreasury;
    }

    function setTreasuryWithSanityModifier(address newTreasury) external onlyOwner checkTreasury {
        treasury = newTreasury;
    }

    function transferOwnershipWithModifierEvent(address newOwner)
        external
        onlyOwner
        emitsOwnershipChange(newOwner)
    {
        owner = newOwner;
    }

    function setPendingOwner(address newPendingOwner) external writesPendingOwner(newPendingOwner) {
        pendingOwner = newPendingOwner;
    }

    function setAdminWithNonAccessModifier(address newAdmin) external nonAccessControl {
        admin = newAdmin;
    }

    function setOwnerViaClearedAlias(address newOwner) external onlyOwner {
        address nextOwner = newOwner;
        nextOwner = address(0x1234);
        owner = nextOwner;
    }

    function unprotectedTransferOwnership(address newOwner) external {
        owner = newOwner;
    }

    function setThreshold(uint256 newThreshold) external onlyOwner {
        threshold = newThreshold;
    }
}

contract MisleadingModifierName {
    address public owner;
    bool public flag = true;

    modifier onlyOwner() {
        require(flag, "paused");
        _;
    }

    function setOwner(address newOwner) external onlyOwner {
        owner = newOwner;
    }
}
