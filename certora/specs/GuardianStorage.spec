/*
 * Spec for linked list reachability for Guardians.
 * This file is derived from OwnerReach.spec for a Safe account.
 * https://github.com/safe-global/safe-smart-account/blob/main/certora/specs/OwnerReach.spec
 *
 * This file uses a reach predicate:
 *    ghost reach(address, address, address) returns bool
 * to represent the transitive of the next
 * relation given by the "owners" field relation for a specific wallet.
 *
 * The idea comes from the paper
 *
 * [1] Itzhaky, S., Banerjee, A., Immerman, N., Nanevski, A., Sagiv, M. (2013).
 *     Effectively-Propositional Reasoning about Reachability in Linked Data Structures.
 *     In: CAV 2013. Springer, https://doi.org/10.1007/978-3-642-39799-8_53
 */

using SafeHarness as safeContract;
using SocialRecoveryModule as socialRecoveryModule;

methods {
    // Safe Functions
    function safeContract.isModuleEnabled(address) external returns (bool) envfree;

    // GuardianManager Functions
    function threshold(address) external returns (uint256) envfree;
    function isGuardian(address, address) external returns (bool) envfree;

}

persistent ghost reach(address, address, address) returns bool {
    init_state axiom forall address X. forall address Y. forall address wallet. reach(wallet, X, Y) == (X == Y || to_mathint(Y) == 0);
}

persistent ghost mapping(address => mapping(address => address)) ghostGuardians {
    init_state axiom forall address wallet. forall address X. to_mathint(ghostGuardians[wallet][X]) == 0;
}

persistent ghost ghostSuccCount(address, address) returns mathint {
    init_state axiom forall address wallet. forall address X. ghostSuccCount(wallet, X) == 0;
}

persistent ghost mapping(address => uint256) ghostGuardianCount {
    init_state axiom forall address X. to_mathint(ghostGuardianCount[X]) == 0;
}

persistent ghost address SENTINEL {
    axiom to_mathint(SENTINEL) == 1;
}

persistent ghost address NULL {
    axiom to_mathint(NULL) == 0;
}

// threshold can be 0 in case no Guardian is set for a wallet.
invariant thresholdSet(address wallet)
    threshold(wallet) <= ghostGuardianCount[wallet]
    {
        preserved {
            requireInvariant reachNull();
            requireInvariant reachInvariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
        }
    }

// every element with 0 in the guardians field can only reach the null pointer and itself
invariant nextNull()
    (forall address wallet. ghostGuardians[wallet][NULL] == 0) &&
    (forall address wallet. forall address X. forall address Y. ghostGuardians[wallet][X] == 0 && reach(wallet, X, Y) => X == Y || Y == 0)
    {
        preserved {
            requireInvariant reachInvariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reachNull();
        }
    }

// every element reaches the 0 pointer (because we replace in reach the end sentinel with null)
invariant reachNull()
    (forall address wallet. forall address X. reach(wallet, X, NULL))
    {
        preserved {
            requireInvariant reachInvariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
        }
    }

// every element that is reachable from another element is either the null pointer or part of the list.
invariant reachableInList()
    (forall address wallet. forall address X. forall address Y. reach(wallet, X, Y) => X == Y || Y == 0 || ghostGuardians[wallet][Y] != 0)
    {
        preserved {
            requireInvariant reachInvariant();
            requireInvariant reachNull();
            requireInvariant inListReachable();
            requireInvariant reachNext();
            requireInvariant nextNull();
            requireInvariant countZeroIffListEmpty();
        }
    }

// reach encodes a linear order. This axiom corresponds to Table 2 in [1].
invariant reachInvariant()
    forall address wallet. forall address X. forall address Y. forall address Z. (
        reach(wallet, X, X)
        && (reach(wallet, X, Y) && reach(wallet, Y, X) => X == Y)
        && (reach(wallet, X, Y) && reach(wallet, Y, Z) => reach(wallet, X, Z))
        && (reach(wallet, X, Y) && reach(wallet, X, Z) => (reach(wallet, Y, Z) || reach(wallet, Z, Y)))
    )
    {
        preserved {
            requireInvariant reachNull();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
        }
    }

// every element with non-zero guardian field is reachable from SENTINEL (head of the list)
invariant inListReachable()
    (forall address wallet. forall address key. ghostGuardians[wallet][key] != 0 => reach(wallet, SENTINEL, key))
    {
        preserved {
            requireInvariant reachInvariant();
            requireInvariant reachNull();
            requireInvariant reachableInList();
            requireInvariant countZeroIffListEmpty();
            requireInvariant emptyListNotReachable();
        }
    }

invariant reachHeadNext()
    forall address wallet. forall address X. (reach(wallet, SENTINEL, X) && X != SENTINEL && X != NULL) =>
           (ghostGuardians[wallet][SENTINEL] != SENTINEL && reach(wallet, ghostGuardians[wallet][SENTINEL], X))
    {   
        preserved {
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reachInvariant();
            requireInvariant reachNull();
            requireInvariant countZeroIffListEmpty();
            requireInvariant emptyListNotReachable();
            requireInvariant nextNull();
        }
    }

// every element reaches its direct successor (except for the tail-SENTINEL).
invariant reachNext()
    forall address wallet. forall address X. reachSucc(wallet, X, ghostGuardians[wallet][X])
    {
        preserved {
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reachNull();
            requireInvariant reachInvariant();
        }
    }

// Express the next relation from the reach relation by stating that it is reachable and there is no other element
// in between.
// This is equivalent to P_next from Table 3.
definition isSucc(address wallet, address a, address b) returns bool = reach(wallet, a, b) && a != b && (forall address Z. reach(wallet, a, Z) && reach(wallet, Z, b) => (a == Z || b == Z));
definition nextOrNull(address n) returns address = n == SENTINEL ? NULL : n;

// Invariant stating that the guardians storage pointers correspond to the next relation, except for the SENTINEL tail marker.
definition reachSucc(address wallet, address key, address next) returns bool =
        (key != NULL && isSucc(wallet, key, nextOrNull(next))) ||
        (key == NULL && next == NULL && (forall address Z. reach(wallet, key, Z) => Z == NULL));

// Update the reach relation when the next pointer of a is changed to b.
// This corresponds to the first two equations in Table 3 [1] (destructive update to break previous paths through a and
// then additionally allow the path to go through the new edge from a to b).
definition updateSucc(address wallet, address a, address b) returns bool =
   forall address W. forall address X. forall address Y. reach@new(W, X, Y) ==
            (X == Y ||
            (reach@old(W, X, Y) && !(W == wallet && reach@old(W, X, a) && a != Y && reach@old(W, a, Y))) ||
            (W == wallet && reach@old(W, X, a) && reach@old(W, b, Y)));

definition countExpected(address wallet, address key) returns mathint =
    ghostGuardians[wallet][key] == NULL ? 0 : ghostGuardians[wallet][key] == SENTINEL ? 1 : ghostSuccCount(wallet, ghostGuardians[wallet][key]) + 1;

definition countSuccessor(address wallet, address key) returns bool = 
    (ghostGuardians[wallet][key] != NULL && ghostGuardians[wallet][key] != SENTINEL => ghostSuccCount(wallet,key) >= 2);
   
definition updateGhostSuccCount(address wallet, address key, mathint diff) returns bool = forall address W. forall address X.
    (ghostSuccCount@new(W, X) == (ghostSuccCount@old(W, X) + (W == wallet && reach(W, X, key) ? diff : 0)));

// hook to update the ghostGuardians and the reach ghost state whenever the entries field
// in storage is written.
// This also checks that the reachSucc invariant is preserved.
hook Sstore currentContract.entries[KEY address wallet].guardians[KEY address key] address value {
    assert key != NULL;
    assert reach(wallet, value, key) => value == SENTINEL, "list is cyclic";
    ghostGuardians[wallet][key] = value;
    havoc reach assuming updateSucc(wallet, key, nextOrNull(value));
    mathint countDiff = countExpected(wallet, key) - ghostSuccCount(wallet, key);
    havoc ghostSuccCount assuming updateGhostSuccCount(wallet, key, countDiff);
}

hook Sstore currentContract.entries[KEY address wallet].count uint256 value {
    ghostGuardianCount[wallet] = value;
}

// Hook to match ghost state and storage state when reading guardians from storage.
// This also provides the reachSucc invariant.
hook Sload address value currentContract.entries[KEY address wallet].guardians[KEY address key] {
    require ghostGuardians[wallet][key] == value;
    require reachSucc(wallet, key, value);
    require ghostSuccCount(wallet, key) == countExpected(wallet, key);
}

hook Sload uint256 value currentContract.entries[KEY address wallet].count {
    // The prover found a counterexample if the guardians count is max uint256,
    // but this is not a realistic scenario.
    require ghostGuardianCount[wallet] < max_uint256;
    require ghostGuardianCount[wallet] == value;
}

invariant countCorrect()
    forall address wallet. forall address X. (ghostSuccCount(wallet, X) == countExpected(wallet, X)) && countSuccessor(wallet, X)
    {
        preserved {
            requireInvariant reachInvariant();
            requireInvariant reachNull();
            requireInvariant inListReachable();
            requireInvariant reachNext();
            requireInvariant nextNull();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
            requireInvariant countZeroIffListEmpty();
        }
    }

invariant guardianCountCorrect()
   forall address wallet. (ghostGuardianCount[wallet] == 0 && ghostGuardians[wallet][SENTINEL] == NULL) || (ghostSuccCount(wallet, SENTINEL) == ghostGuardianCount[wallet] + 1)
    {
        preserved {
            requireInvariant reachInvariant();
            requireInvariant reachNull();
            requireInvariant inListReachable();
            requireInvariant reachNext();
            requireInvariant nextNull();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
        }
    }

invariant countZeroIffListEmpty()
    forall address wallet. ghostGuardianCount[wallet] == 0 <=>
        (ghostGuardians[wallet][SENTINEL] == NULL || ghostGuardians[wallet][SENTINEL] == SENTINEL)
    {
        preserved {
            requireInvariant reachInvariant();
            requireInvariant reachNull();
            requireInvariant inListReachable();
            requireInvariant reachNext();
            requireInvariant nextNull();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
            requireInvariant countCorrect();
            requireInvariant guardiancountCorrect();
        }
    }

invariant emptyListNotReachable()
    forall address wallet. (ghostGuardians[wallet][SENTINEL] == NULL || ghostGuardians[wallet][SENTINEL] == SENTINEL)
        => (forall address X. X != SENTINEL => ghostGuardians[wallet][X] == NULL)
    {
        preserved {
            requireInvariant reachInvariant();
            requireInvariant reachNull();
            requireInvariant inListReachable();
            requireInvariant reachNext();
            requireInvariant nextNull();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
            requireInvariant countCorrect();
            requireInvariant guardiancountCorrect();
        }
    }

rule storeHookPreservesInvariants(address wallet, address key, address value) {
    // These are checked in the hook.
    require key != NULL;
    require reach(wallet, value, key) => value == SENTINEL; //, "list is cyclic";

    // Invariants that hold even in the middle
    requireInvariant reachNull();
    requireInvariant reachInvariant();

    address someKey;
    address someWallet;
    require reachSucc(someWallet, someKey, ghostGuardians[someWallet][someKey]);
    require ghostSuccCount(someWallet, someKey) == countExpected(someWallet, someKey);
    ghostGuardians[wallet][key] = value;
    havoc reach assuming updateSucc(wallet, key, nextOrNull(value));
    mathint countDiff = countExpected(wallet, key) - ghostSuccCount(wallet, key);
    havoc ghostSuccCount assuming updateGhostSuccCount(wallet, key, countDiff);
    assert reachSucc(someWallet, someKey, ghostGuardians[someWallet][someKey]), "reachSucc violated after guardians update";
    assert ghostSuccCount(someWallet, someKey) == countExpected(someWallet, someKey);

    // assert also the invariants used above
    assert (forall address W. forall address X. reach(W, X, NULL));
    assert (forall address W. forall address X. forall address Y. forall address Z.
        reach(W, X, X)
        && (reach(W, X, Y) && reach(W, Y, X) => X == Y)
        && (reach(W, X, Y) && reach(W, Y, Z) => reach(W, X, Z))
        && (reach(W, X, Y) && reach(W, X, Z) => (reach(W, Y, Z) || reach(W, Z, Y)))
    );
}

rule isGuardianDoesNotRevert {
    address addr;
    isGuardian@withrevert(safeContract, addr);
    assert !lastReverted, "isGuardian should not revert";
}

rule sentinelCantBeGuardian() {
   assert !isGuardian(safeContract, SENTINEL), "SENTINEL must not be guardian";
}

rule isGuardianInList {
    address addr;
    env e;
    require safeContract.isModuleEnabled(e.msg.sender);
    require addr != SENTINEL;
    bool result = isGuardian(safeContract, addr);
    assert result == (ghostGuardians[safeContract][addr] != NULL), "isGuardian returns wrong result";
}

rule addGuardianChangesEntries {
    address other;
    address toAdd;
    uint256 threshold;
    env e;
    require safeContract.isModuleEnabled(e.msg.sender);

    requireInvariant reachNull();
    requireInvariant reachInvariant();
    requireInvariant inListReachable();
    requireInvariant reachableInList();
    requireInvariant countZeroIffListEmpty();
    require other != toAdd;
    bool isGuardianOtherBefore = isGuardian(safeContract, other);
    addGuardianWithThreshold(e, safeContract, toAdd, threshold);

    assert isGuardian(safeContract, toAdd), "addGuardian should add the given guardian";
    assert isGuardian(safeContract, other) == isGuardianOtherBefore, "addGuardian should not remove or add other guardians";
}

rule removeGuardianChangesGuardians {
    address other;
    address toRemove;
    address prevGuardian;
    uint256 threshold;
    env e;
    require safeContract.isModuleEnabled(e.msg.sender);

    requireInvariant reachNull();
    requireInvariant reachInvariant();
    requireInvariant inListReachable();
    requireInvariant reachableInList();
    require other != toRemove;
    bool isGuardianOtherBefore = isGuardian(safeContract, other);
    revokeGuardianWithThreshold(e, safeContract, prevGuardian, toRemove, threshold);

    assert !isGuardian(safeContract, toRemove), "revokeGuardian should remove the given guardian";
    assert isGuardian(safeContract, other) == isGuardianOtherBefore, "revokeGuardian should not remove or add other guardians";
}
