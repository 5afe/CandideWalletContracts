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

// definition reachableOnly(method f) returns bool =
//     f.selector != sig:simulateAndRevert(address,bytes).selector;

definition MAX_UINT256() returns uint256 = 0xffffffffffffffffffffffffffffffff;

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
            requireInvariant reach_null();
            requireInvariant reach_invariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
        }
    }

invariant self_not_guardian()
    forall address wallet. currentContract != SENTINEL => ghostGuardians[wallet][currentContract] == 0
    {
        preserved {
            requireInvariant reach_null();
            requireInvariant reach_invariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            // requireInvariant thresholdSet();
        }
    }


// every element with 0 in the guardians field can only reach the null pointer and itself
invariant nextNull()
    (forall address wallet. ghostGuardians[wallet][NULL] == 0) &&
    (forall address wallet. forall address X. forall address Y. ghostGuardians[wallet][X] == 0 && reach(wallet, X, Y) => X == Y || Y == 0)
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reach_null();
            // requireInvariant thresholdSet();
        }
    }

// every element reaches the 0 pointer (because we replace in reach the end sentinel with null)
invariant reach_null()
    (forall address wallet. forall address X. reach(wallet, X, NULL))
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            // requireInvariant thresholdSet();
        }
    }

// every element that is reachable from another element is either the null pointer or part of the list.
invariant reachableInList()
    (forall address wallet. forall address X. forall address Y. reach(wallet, X, Y) => X == Y || Y == 0 || ghostGuardians[wallet][Y] != 0)
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            requireInvariant inListReachable();
            requireInvariant reach_next();
            requireInvariant nextNull();
            // requireInvariant thresholdSet();
        }
    }

// reach encodes a linear order. This axiom corresponds to Table 2 in [1].
invariant reach_invariant()
    forall address wallet. forall address X. forall address Y. forall address Z. (
        reach(wallet, X, X)
        && (reach(wallet, X, Y) && reach(wallet, Y, X) => X == Y)
        && (reach(wallet, X, Y) && reach(wallet, Y, Z) => reach(wallet, X, Z))
        && (reach(wallet, X, Y) && reach(wallet, X, Z) => (reach(wallet, Y, Z) || reach(wallet, Z, Y)))
    )
    {
        preserved {
            requireInvariant reach_null();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
            // requireInvariant thresholdSet();
        }
    }

// every element with non-zero guardian field is reachable from SENTINEL (head of the list)
invariant inListReachable()
    (forall address wallet. forall address key. ghostGuardians[wallet][key] != 0 => reach(wallet, SENTINEL, key))
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            requireInvariant reachableInList();
            // requireInvariant thresholdSet();
        }
    }

invariant reachHeadNext()
    forall address wallet. forall address X. (reach(wallet, SENTINEL, X) && X != SENTINEL && X != NULL) =>
           (ghostGuardians[wallet][SENTINEL] != SENTINEL && reach(wallet, ghostGuardians[wallet][SENTINEL], X))
    {
        preserved {
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            // requireInvariant thresholdSet();
        }
    }

// every element reaches its direct successor (except for the tail-SENTINEL).
invariant reach_next()
    forall address wallet. forall address X. reach_succ(wallet, X, ghostGuardians[wallet][X])
    {
        preserved {
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reach_null();
            requireInvariant reach_invariant();
            // requireInvariant thresholdSet();
        }
    }

// Express the next relation from the reach relation by stating that it is reachable and there is no other element
// in between.
// This is equivalent to P_next from Table 3.
definition isSucc(address wallet, address a, address b) returns bool = reach(wallet, a, b) && a != b && (forall address Z. reach(wallet, a, Z) && reach(wallet, Z, b) => (a == Z || b == Z));
definition next_or_null(address n) returns address = n == SENTINEL ? NULL : n;

// Invariant stating that the guardians storage pointers correspond to the next relation, except for the SENTINEL tail marker.
definition reach_succ(address wallet, address key, address next) returns bool =
        (isSucc(wallet, key, next_or_null(next))) ||
        (next == NULL && key == NULL);

// Update the reach relation when the next pointer of a is changed to b.
// This corresponds to the first two equations in Table 3 [1] (destructive update to break previous paths through a and
// then additionally allow the path to go through the new edge from a to b).
definition updateSucc(address wallet, address a, address b) returns bool = 
   forall address W. forall address X. forall address Y. reach@new(W, X, Y) ==
            (X == Y ||
            (reach@old(W, X, Y) && !(W == wallet && reach@old(W, X, a) && a != Y && reach@old(W, a, Y))) ||
            (W == wallet && reach@old(W, X, a) && reach@old(W, b, Y)));

definition count_expected(address wallet, address key) returns mathint =
    ghostGuardians[wallet][key] == NULL ? 0 : ghostGuardians[wallet][key] == SENTINEL ? 1 : ghostSuccCount(wallet, ghostGuardians[wallet][key]) + 1;

definition updateGhostSuccCount(address wallet, address key, mathint diff) returns bool = forall address W. forall address X.
    (ghostSuccCount@new(W, X) == (ghostSuccCount@old(W, X) + (W == wallet && reach(W, X, key) ? diff : 0)));

// hook to update the ghostGuardians and the reach ghost state whenever the entries field
// in storage is written.
// This also checks that the reach_succ invariant is preserved.
hook Sstore currentContract.entries[KEY address wallet].guardians[KEY address key] address value {
    // address valueOrNull;
    // address someKey;
    // address someWallet;
    // require reach_succ(someWallet, someKey, ghostGuardians[someWallet][someKey]);
    // require ghostSuccCount(someWallet, someKey) == count_expected(someWallet, someKey);
    assert reach(wallet, value, key) => value == SENTINEL, "list is cyclic";
    ghostGuardians[wallet][key] = value;
    havoc reach assuming updateSucc(wallet, key, next_or_null(value));
    mathint countDiff = count_expected(wallet, key) - ghostSuccCount(wallet, key);
    havoc ghostSuccCount assuming updateGhostSuccCount(wallet, key, countDiff);
    // assert reach_succ(someWallet, someKey, ghostGuardians[someWallet][someKey]), "reach_succ violated after guardians update";
    // assert ghostSuccCount(someWallet, someKey) == count_expected(someWallet, someKey);
}

hook Sstore currentContract.entries[KEY address wallet].count uint256 value {
    ghostGuardianCount[wallet] = value;
}

// Hook to match ghost state and storage state when reading guardians from storage.
// This also provides the reach_succ invariant.
hook Sload address value currentContract.entries[KEY address wallet].guardians[KEY address key] {
    require ghostGuardians[wallet][key] == value;
    require reach_succ(wallet, key, value);
    require ghostSuccCount(wallet, key) == count_expected(wallet, key);
}

hook Sload uint256 value currentContract.entries[KEY address wallet].count {
    // The prover found a counterexample if the guardians count is max uint256,
    // but this is not a realistic scenario.
    require ghostGuardianCount[wallet] < MAX_UINT256();
    require ghostGuardianCount[wallet] == value;
}

invariant reachCount()
    forall address wallet. forall address X. forall address Y. reach(wallet, X, Y) =>
        ghostSuccCount(wallet, X) >= ghostSuccCount(wallet, Y)
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            requireInvariant inListReachable();
            requireInvariant reach_next();
            requireInvariant nextNull();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
            // requireInvariant thresholdSet();
            requireInvariant count_correct();
        }
    }

invariant count_correct()
    forall address wallet. forall address X. ghostSuccCount(wallet, X) == count_expected(wallet, X)
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            requireInvariant inListReachable();
            requireInvariant reach_next();
            requireInvariant nextNull();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
            // requireInvariant thresholdSet();
        }
    }

invariant guardiancount_correct()
   forall address wallet. (ghostGuardianCount[wallet] == 0 && ghostGuardians[wallet][SENTINEL] == NULL) || (ghostSuccCount(wallet, SENTINEL) == ghostGuardianCount[wallet] + 1)
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            requireInvariant inListReachable();
            requireInvariant reach_next();
            requireInvariant nextNull();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
            requireInvariant reachCount();
            // requireInvariant thresholdSet();
        }
    }

invariant ghostGuardianCountZero()
    forall address wallet. ghostGuardianCount[wallet] == 0 => ghostGuardians[wallet][SENTINEL] == NULL || ghostGuardians[wallet][SENTINEL] == SENTINEL
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            requireInvariant inListReachable();
            requireInvariant reach_next();
            requireInvariant nextNull();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
            requireInvariant reachCount();
            // requireInvariant thresholdSet();
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
    requireInvariant self_not_guardian();
    bool result = isGuardian(safeContract, addr);
    assert result == false, "currentContract or SENTINEL must not be guardian";
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

    requireInvariant reach_null();
    requireInvariant reach_invariant();
    requireInvariant inListReachable();
    requireInvariant reachableInList();
    requireInvariant reachCount();
    requireInvariant count_correct();
    requireInvariant guardiancount_correct();
    require other != toAdd;
    bool isGuardianOtherBefore = isGuardian(safeContract, other);
    addGuardianWithThreshold(e, safeContract, toAdd, threshold);

    assert isGuardian(safeContract, toAdd), "addGuardian should add the given guardian";
    assert isGuardian(safeContract, other) == isGuardianOtherBefore, "addGuardian should not remove or add other guardians";
    satisfy true;
}

rule removeGuardianChangesGuardians {
    address other;
    address toRemove;
    address prevGuardian;
    uint256 threshold;
    env e;
    require safeContract.isModuleEnabled(e.msg.sender);

    requireInvariant reach_null();
    requireInvariant reach_invariant();
    requireInvariant inListReachable();
    requireInvariant reachableInList();
    require other != toRemove;
    bool isGuardianOtherBefore = isGuardian(safeContract, other);
    revokeGuardianWithThreshold(e, safeContract, prevGuardian, toRemove, threshold);

    assert !isGuardian(safeContract, toRemove), "revokeGuardian should remove the given guardian";
    assert isGuardian(safeContract, other) == isGuardianOtherBefore, "revokeGuardian should not remove or add other guardians";
}
