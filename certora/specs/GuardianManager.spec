/*
 * Spec for linked list reachability for Guardians.
 * This file is derived from OwnerReach.spec for a Safe account.
 * https://github.com/safe-global/safe-smart-account/blob/main/certora/specs/OwnerReach.spec
 * 
 * This file uses a reach predicate:
 *    ghost reach(address, address) returns bool
 * to represent the transitive relation of the next
 * relation given byt the "owners" field.
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

// definition reachableOnly(method f) returns bool =
//     f.selector != sig:simulateAndRevert(address,bytes).selector;


definition MAX_UINT256() returns uint256 = 0xffffffffffffffffffffffffffffffff;

persistent ghost reach(address, address) returns bool {
    init_state axiom forall address X. forall address Y. reach(X, Y) == (X == Y || to_mathint(Y) == 0);
}

persistent ghost mapping(address => mapping(address => address)) ghostOwners {
    init_state axiom forall address Y. forall address X. to_mathint(ghostOwners[Y][X]) == 0;
}

persistent ghost ghostSuccCount(address) returns mathint {
    init_state axiom forall address X. ghostSuccCount(X) == 0;
}

persistent ghost mapping(address => uint256) ghostOwnerCount;

persistent ghost address SENTINEL {
    axiom to_mathint(SENTINEL) == 1;
}

persistent ghost address NULL {
    axiom to_mathint(NULL) == 0;
}

// threshold can be 0 in case on Guardian is set for a wallet.
invariant thresholdSet(address wallet) threshold(wallet) <= ghostOwnerCount[wallet]
    {
        preserved {
            requireInvariant reach_null(wallet);
            requireInvariant reach_invariant(wallet);
            requireInvariant inListReachable(wallet);
            requireInvariant reachableInList(wallet);
        }
    }

invariant self_not_owner(address wallet) currentContract != SENTINEL => ghostOwners[wallet][currentContract] == 0
    {
        preserved {
            requireInvariant reach_null(wallet);
            requireInvariant reach_invariant(wallet);
            requireInvariant inListReachable(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }


// every element with 0 in the owners field can only reach the null pointer and itself
invariant nextNull(address wallet)
    ghostOwners[wallet][NULL] == 0 &&
    (forall address X. forall address Y. ghostOwners[wallet][X] == 0 && reach(X, Y) => X == Y || Y == 0)
    {
        preserved {
            requireInvariant reach_invariant(wallet);
            requireInvariant inListReachable(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant reach_null(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }

// every element reaches the 0 pointer (because we replace in reach the end sentinel with null)
invariant reach_null(address wallet)
    (forall address X. reach(X, NULL))
    {
        preserved {
            requireInvariant reach_invariant(wallet);
            requireInvariant inListReachable(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }

// every element that is reachable from another element is either the null pointer or part of the list.
invariant reachableInList(address wallet)
    (forall address X. forall address Y. reach(X, Y) => X == Y || Y == 0 || ghostOwners[wallet][Y] != 0)
    {
        preserved {
            requireInvariant reach_invariant(wallet);
            requireInvariant reach_null(wallet);
            requireInvariant inListReachable(wallet);
            requireInvariant reach_next(wallet);
            requireInvariant nextNull(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }

// reach encodes a linear order. This axiom corresponds to Table 2 in [1].
invariant reach_invariant(address wallet)
    forall address X. forall address Y. forall address Z. (
        reach(X, X)
        && (reach(X,Y) && reach (Y, X) => X == Y)
        && (reach(X,Y) && reach (Y, Z) => reach(X, Z))
        && (reach(X,Y) && reach (X, Z) => (reach(Y,Z) || reach(Z,Y)))
    )
    {
        preserved {
            requireInvariant reach_null(wallet);
            requireInvariant inListReachable(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant reachHeadNext(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }

// every element with non-zero owner field is reachable from SENTINEL (head of the list)
invariant inListReachable(address wallet)
    ghostOwners[wallet][SENTINEL] != 0 &&
    (forall address key. ghostOwners[wallet][key] != 0 => reach(SENTINEL, key))
    {
        preserved {
            requireInvariant thresholdSet(wallet);
            requireInvariant reach_invariant(wallet);
            requireInvariant reach_null(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }

invariant reachHeadNext(address wallet)
    forall address Y. forall address X. reach(SENTINEL, X) && X != SENTINEL && X != NULL =>
           ghostOwners[Y][SENTINEL] != SENTINEL && reach(ghostOwners[Y][SENTINEL], X)
    {
        preserved {
            requireInvariant inListReachable(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant reach_invariant(wallet);
            requireInvariant reach_null(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }

// every element reaches its direct successor (except for the tail-SENTINEL).
invariant reach_next(address wallet)
    forall address X. reach_succ(X, ghostOwners[wallet][X])
    {
        preserved {
            requireInvariant inListReachable(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant reach_null(wallet);
            requireInvariant reach_invariant(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }

// Express the next relation from the reach relation by stating that it is reachable and there is no other element
// in between.
// This is equivalent to P_next from Table 3.
definition isSucc(address a, address b) returns bool = reach(a, b) && a != b && (forall address Z. reach(a, Z) && reach(Z, b) => (a == Z || b == Z));
definition next_or_null(address n) returns address = n == SENTINEL ? NULL : n;

// Invariant stating that the owners storage pointers correspond to the next relation, except for the SENTINEL tail marker.
definition reach_succ(address key, address next) returns bool =
        (isSucc(key, next_or_null(next))) ||
        (next == NULL && key == NULL);

// Update the reach relation when the next pointer of a is changed to b.
// This corresponds to the first two equations in Table 3 [1] (destructive update to break previous paths through a and
// then additionally allow the path to go through the new edge from a to b).
definition updateSucc(address a, address b) returns bool = forall address X. forall address Y. reach@new(X, Y) ==
            (X == Y ||
            (reach@old(X, Y) && !(reach@old(X, a) && a != Y && reach@old(a, Y))) ||
            (reach@old(X, a) && reach@old(b, Y)));

definition count_expected(address wallet, address key) returns mathint =
    ghostOwners[wallet][key] == NULL ? 0 : ghostOwners[wallet][key] == SENTINEL ? 1 : ghostSuccCount(ghostOwners[wallet][key]) + 1;

definition updateGhostSuccCount(address key, mathint diff) returns bool = forall address X.
    ghostSuccCount@new(X) == ghostSuccCount@old(X) + (reach(X, key) ? diff : 0);

// hook to update the ghostOwners and the reach ghost state whenever the entries field
// in storage is written.
// This also checks that the reach_succ invariant is preserved.
hook Sstore currentContract.entries[KEY address wallet].guardians[KEY address key] address value {
    address valueOrNull;
    address someKey;
    require reach_succ(someKey, ghostOwners[wallet][someKey]);
    require ghostSuccCount(someKey) == count_expected(wallet, someKey);
    assert reach(value, key) => value == SENTINEL, "list is cyclic";
    ghostOwners[wallet][key] = value;
    havoc reach assuming updateSucc(key, next_or_null(value));
    mathint countDiff = count_expected(wallet, key) - ghostSuccCount(key);
    havoc ghostSuccCount assuming updateGhostSuccCount(key, countDiff);
    assert reach_succ(someKey, ghostOwners[wallet][someKey]), "reach_succ violated after owners update";
    assert ghostSuccCount(someKey) == count_expected(wallet, someKey);
}

hook Sstore currentContract.entries[KEY address wallet].count uint256 value {
    ghostOwnerCount[wallet] = value;
}

// Hook to match ghost state and storage state when reading owners from storage.
// This also provides the reach_succ invariant.
hook Sload address value currentContract.entries[KEY address wallet].guardians[KEY address key] {
    require ghostOwners[wallet][key] == value;
    require reach_succ(key, value);
    require ghostSuccCount(key) == count_expected(wallet, key);
}

hook Sload uint256 value currentContract.entries[KEY address wallet].count {
    // The prover found a counterexample if the owners count is max uint256,
    // but this is not a realistic scenario.
    require ghostOwnerCount[wallet] < MAX_UINT256();
    require ghostOwnerCount[wallet] == value;
}

invariant reachCount(address wallet)
    forall address X. forall address Y. reach(X, Y) =>
        ghostSuccCount(X) >= ghostSuccCount(Y)
    {
        preserved {
            requireInvariant reach_invariant(wallet);
            requireInvariant reach_null(wallet);
            requireInvariant inListReachable(wallet);
            requireInvariant reach_next(wallet);
            requireInvariant nextNull(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant reachHeadNext(wallet);
            requireInvariant thresholdSet(wallet);
            requireInvariant count_correct(wallet);
        }
    }

invariant count_correct(address wallet)
    forall address Y. forall address X. ghostSuccCount(X) == count_expected(Y, X)
    {
        preserved {
            requireInvariant reach_invariant(wallet);
            requireInvariant reach_null(wallet);
            requireInvariant inListReachable(wallet);
            requireInvariant reach_next(wallet);
            requireInvariant nextNull(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant reachHeadNext(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }


invariant ownercount_correct(address wallet)
    ghostSuccCount(SENTINEL) == ghostOwnerCount[wallet] + 1
    {
        preserved {
            requireInvariant reach_invariant(wallet);
            requireInvariant reach_null(wallet);
            requireInvariant inListReachable(wallet);
            requireInvariant reach_next(wallet);
            requireInvariant nextNull(wallet);
            requireInvariant reachableInList(wallet);
            requireInvariant reachHeadNext(wallet);
            requireInvariant reachCount(wallet);
            requireInvariant thresholdSet(wallet);
        }
    }

rule isGuardianDoesNotRevert {
    address addr;
    isGuardian@withrevert(safeContract, addr);
    assert !lastReverted, "isGuardian should not revert";
}

rule isGuardianNotSelfOrSentinal {
    address addr;
    require addr == currentContract || addr == SENTINEL;
    requireInvariant self_not_owner(safeContract);
    bool result = isGuardian(safeContract, addr);
    assert result == false, "currentContract or SENTINEL must not be guardian";
}

rule isGuardianInList {
    address addr;
    env e;
    require safeContract.isModuleEnabled(e.msg.sender);
    require addr != SENTINEL;
    bool result = isGuardian(safeContract, addr);
    assert result == (ghostOwners[safeContract][addr] != NULL), "isGuardian returns wrong result";
}

rule addGuardianChangesEntries {
    address other;
    address toAdd;
    uint256 threshold;
    env e;
    require safeContract.isModuleEnabled(e.msg.sender);

    requireInvariant reach_null(safeContract);
    requireInvariant reach_invariant(safeContract);
    requireInvariant inListReachable(safeContract);
    requireInvariant reachableInList(safeContract);
    require other != toAdd;
    bool isGuardianOtherBefore = isGuardian(safeContract, other);
    addGuardian(e, safeContract, toAdd);

    assert isGuardian(safeContract, toAdd), "addOwner should add the given owner";
    assert isGuardian(safeContract, other) == isGuardianOtherBefore, "addOwner should not remove or add other owners";
}

rule removeGuardianChangesOwners {
    address other;
    address toRemove;
    address prevOwner;
    uint256 threshold;
    env e;
    require safeContract.isModuleEnabled(e.msg.sender);

    requireInvariant reach_null(safeContract);
    requireInvariant reach_invariant(safeContract);
    requireInvariant inListReachable(safeContract);
    requireInvariant reachableInList(safeContract);
    require other != toRemove;
    bool isGuardianOtherBefore = isGuardian(safeContract, other);
    revokeGuardian(e, safeContract, prevOwner, toRemove);

    assert !isGuardian(safeContract, toRemove), "revokeGuardian should remove the given guardian";
    assert isGuardian(safeContract, other) == isGuardianOtherBefore, "revokeGuardian should not remove or add other guardians";
}
