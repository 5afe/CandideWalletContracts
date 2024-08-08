/*
 * Spec for linked list reachability.
 *
 * This file uses a reach predicate:
 *    ghost ghostReach(address, address) returns bool
 * to represent the transitive relation of the next
 * relation given by the "owners" field.
 *
 * The idea comes from the paper
 *
 * [1] Itzhaky, S., Banerjee, A., Immerman, N., Nanevski, A., Sagiv, M. (2013).
 *     Effectively-Propositional Reasoning about Reachability in Linked Data Structures.
 *     In: CAV 2013. Springer, https://doi.org/10.1007/978-3-642-39799-8_53
 */
using SafeHarness as safeContract;

methods {
    // Social Recovery Module Functions
    function isGuardian(address, address) external returns (bool) envfree;
    function guardiansCount(address) external returns (uint256) envfree;
    function threshold(address) external returns (uint256) envfree;
    function nonce(address) external returns (uint256) envfree;
    function getRecoveryHash(address, address[], uint256, uint256) external returns (bytes32) envfree;
    function getRecoveryApprovals(address, address[], uint256) external returns (uint256) envfree;
    function getRecoveryApprovalsWithNonce(address, address[], uint256, uint256) external returns (uint256) envfree;
    function countGuardians(address) external returns (uint256) envfree;
    function hasGuardianApproved(address, address, address[], uint256) external returns (bool) envfree;

    // Safe Functions
    function safeContract.isModuleEnabled(address module) external returns (bool) envfree;
    function safeContract.isOwner(address owner) external returns (bool) envfree;
    function safeContract.getOwners() external returns (address[] memory) envfree;
    function safeContract.getThreshold() external returns (uint256) envfree;

    // Wildcard Functions
    function _.execTransactionFromModule(address to, uint256 value, bytes data, Enum.Operation operation) external => DISPATCHER(true);
    function _.isModuleEnabled(address module) external => DISPATCHER(false);
    function _.isOwner(address owner) external => DISPATCHER(false);
    function _.getOwners() external => DISPATCHER(false);
    function _._ external => DISPATCH[safeContract.removeOwner(address,address,uint256),
                            safeContract.addOwnerWithThreshold(address,uint256),
                            safeContract.swapOwner(address,address,address)] default NONDET;
    

    // additional summarizations as NONDET DELETE
    function _.getStorageAt(uint256 offset, uint256 length) external => NONDET DELETE;
    function _.checkNSignatures(bytes32,bytes,bytes,uint256) external => NONDET DELETE;
    function _.getModulesPaginated(address,uint256) external => NONDET DELETE;
    function _.execTransaction(address,uint256,bytes,Enum.Operation,uint256,uint256,uint256,address,address,bytes) external => NONDET DELETE;
    function _.execTransactionFromModuleReturnData(address,uint256,bytes,Enum.Operation) external => NONDET DELETE;
    function _.checkSignatures(bytes32,bytes,bytes) external => NONDET DELETE;
    function _.executeRecovery(address,address[],uint256) external => NONDET DELETE;
    function _.simulateAndRevert(address,bytes) external => NONDET DELETE;
    function _.confirmRecovery(address,address[],uint256,bool) external => NONDET DELETE;
    function _.getGuardians(address) external => NONDET DELETE;
    function _.getTransactionHash(address,uint256,bytes,Enum.Operation,uint256,uint256,uint256,address,address,uint256) external => NONDET DELETE;
    function _.encodeTransactionData(address,uint256,bytes,Enum.Operation,uint256,uint256,uint256,address,address,uint256) external => NONDET DELETE;
    function _.multiConfirmRecovery(address,address[],uint256,SocialRecoveryModule.SignatureData[],bool) external => NONDET DELETE;
    function _.setup(address[],uint256,address,bytes,address,address,uint256,address) external => NONDET DELETE;
}

definition reachableOnly(method f) returns bool =
    f.selector != sig:safeContract.simulateAndRevert(address,bytes).selector;

// A ghost function to check the reachability for given two addresses.
persistent ghost ghostReach(address, address) returns bool {
    init_state axiom forall address X. forall address Y. ghostReach(X, Y) == (X == Y || to_mathint(Y) == 0);
}

// A ghost mapping to store the owners of Safe. This is required because CVL does not allow calling 
// contract functions in quantifiers.
persistent ghost mapping(address => address) ghostOwners {
    init_state axiom forall address X. to_mathint(ghostOwners[X]) == 0;
}

// A ghost function to store the number of successors for each owner for a given wallet address.
// This is used to verify the count of owners for a given wallet address.
persistent ghost ghostSuccCount(address) returns mathint {
    init_state axiom forall address X. ghostSuccCount(X) == 0;
}

// A ghost variable to store the number of owners in the Safe.
persistent ghost uint256 ghostOwnerCount;

persistent ghost address SENTINEL {
    axiom to_mathint(SENTINEL) == 1;
}

persistent ghost address NULL {
    axiom to_mathint(NULL) == 0;
}

// This invariant ensures that the threshold is non-zero and less than equal owner count.
invariant thresholdSet() safeContract.getThreshold() > 0  && safeContract.getThreshold() <= ghostOwnerCount
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant reach_null();
            requireInvariant reach_invariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
        }
    }

// SoicalRecoveryModule should not be an owner.
invariant self_not_owner() currentContract != SENTINEL => ghostOwners[currentContract] == 0
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant reach_null();
            requireInvariant reach_invariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant thresholdSet();
        }
    }

// Every element with 0 in the owners field can only reach the null pointer and itself
invariant nextNull()
    ghostOwners[NULL] == 0 &&
    (forall address X. forall address Y. ghostOwners[X] == 0 && ghostReach(X, Y) => X == Y || Y == 0)
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reach_null();
            requireInvariant thresholdSet();
        }
    }

// Every element reaches the 0 pointer (because we replace in reach the end sentinel with null)
invariant reach_null()
    (forall address X. ghostReach(X, NULL))
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant thresholdSet();
        }
    }

// Every element with non-zero owner field is reachable from SENTINEL (head of the list)
invariant inListReachable()
    ghostOwners[SENTINEL] != 0 &&
    (forall address key. ghostOwners[key] != 0 => ghostReach(SENTINEL, key))
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant thresholdSet();
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            requireInvariant reachableInList();
            requireInvariant thresholdSet();
        }
    }

// Every element that is reachable from another element is either the null pointer or part of the list.
invariant reachableInList()
    (forall address X. forall address Y. ghostReach(X, Y) => X == Y || Y == 0 || ghostOwners[Y] != 0)
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            requireInvariant inListReachable();
            requireInvariant reach_next();
            requireInvariant nextNull();
            requireInvariant thresholdSet();
        }
    }

// Checks that every element reachable from SENTINEL is part of the owners list.
invariant reachHeadNext()
    forall address X. ghostReach(SENTINEL, X) && X != SENTINEL && X != NULL =>
           ghostOwners[SENTINEL] != SENTINEL && ghostReach(ghostOwners[SENTINEL], X)
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reach_invariant();
            requireInvariant reach_null();
            requireInvariant thresholdSet();
        }
    }

// ghostReach encodes a linear order. This axiom corresponds to Table 2 in [1].
invariant reach_invariant()
    forall address X. forall address Y. forall address Z. (
        ghostReach(X, X)
        && (ghostReach(X,Y) && ghostReach (Y, X) => X == Y)
        && (ghostReach(X,Y) && ghostReach (Y, Z) => ghostReach(X, Z))
        && (ghostReach(X,Y) && ghostReach (X, Z) => (ghostReach(Y,Z) || ghostReach(Z,Y)))
    )
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant reach_null();
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reachHeadNext();
            requireInvariant thresholdSet();
        }
    }

// Every element reaches its direct successor (except for the tail-SENTINEL).
invariant reach_next()
    forall address X. reach_succ(X, ghostOwners[X])
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reach_null();
            requireInvariant reach_invariant();
            requireInvariant thresholdSet();
        }
    }

// The number of elements in the list is equal to the number of elements reachable from the SENTINEL.
invariant ownerCountEqualsSentinelSuccessor() safeContract.getOwners().length + 1 == ghostSuccCount(SENTINEL) 
    filtered { f -> reachableOnly(f) }
    {
        preserved {
            requireInvariant inListReachable();
            requireInvariant reachableInList();
            requireInvariant reach_null();
            requireInvariant reach_invariant();
            requireInvariant thresholdSet();
        }
    }

// Express the next relation from the reach relation by stating that it is reachable and there is no other element
// in between.
// This is equivalent to P_next from Table 3.
definition isSucc(address a, address b) returns bool = ghostReach(a, b) && a != b && (forall address Z. ghostReach(a, Z) && ghostReach(Z, b) => (a == Z || b == Z));
definition next_or_null(address n) returns address = n == SENTINEL ? NULL : n;

// Invariant stating that the owners storage pointers correspond to the next relation, except for the SENTINEL tail marker.
definition reach_succ(address key, address next) returns bool =
        (isSucc(key, next_or_null(next))) ||
        (next == NULL && key == NULL);

// Update the reach relation when the next pointer of a is changed to b.
// This corresponds to the first two equations in Table 3 [1] (destructive update to break previous paths through a and
// then additionally allow the path to go through the new edge from a to b).
definition updateSucc(address a, address b) returns bool = forall address X. forall address Y. ghostReach@new(X, Y) ==
            (X == Y ||
            (ghostReach@old(X, Y) && !(ghostReach@old(X, a) && a != Y && ghostReach@old(a, Y))) ||
            (ghostReach@old(X, a) && ghostReach@old(b, Y)));

definition count_expected(address key) returns mathint =
    ghostOwners[key] == NULL ? 0 : ghostOwners[key] == SENTINEL ? 1 : ghostSuccCount(ghostOwners[key]) + 1;

definition updateGhostSuccCount(address key, mathint diff) returns bool = forall address X.
    ghostSuccCount@new(X) == ghostSuccCount@old(X) + (ghostReach(X, key) ? diff : 0);

// Hook to update the ghostOwners and the reach ghost state whenever the owners field
// in storage is written.
// This also checks that the reach_succ invariant is preserved.
hook Sstore safeContract.owners[KEY address key] address value {
    address valueOrNull;
    address someKey;
    require reach_succ(someKey, ghostOwners[someKey]);
    require ghostSuccCount(someKey) == count_expected(someKey);
    assert ghostReach(value, key) => value == SENTINEL, "list is cyclic";
    ghostOwners[key] = value;
    havoc ghostReach assuming updateSucc(key, next_or_null(value));
    mathint countDiff = count_expected(key) - ghostSuccCount(key);
    havoc ghostSuccCount assuming updateGhostSuccCount(key, countDiff);
    assert reach_succ(someKey, ghostOwners[someKey]), "reach_succ violated after owners update";
    assert ghostSuccCount(someKey) == count_expected(someKey);
}

// Hook to update the ghostOwnerCount whenever the ownerCount field in storage is written.
hook Sstore safeContract.ownerCount uint256 value {
    ghostOwnerCount = value;
}

// Hook to match ghost state and storage state when reading owners from storage.
// This also provides the reach_succ invariant.
hook Sload address value safeContract.owners[KEY address key] {
    require ghostOwners[key] == value;
    require reach_succ(key, value);
    require ghostSuccCount(key) == count_expected(key);
}

// Hook to match ghost state and storage state when reading ownerCount from storage.
// This also ensures that ownerCount does not exceed the maximum value of uint256.
hook Sload uint256 value safeContract.ownerCount {
    // The prover found a counterexample if the owners count is max uint256,
    // but this is not a realistic scenario.
    require ghostOwnerCount < max_uint256;
    require ghostOwnerCount == value;
}

// Helper functions to be used in rules that require the recovery to be initiated.
// Pending recovery means:
// - a non-zero `executeAfter` timestamp in the `recoveryRequests` mapping (the smart contract checks it the same way)
// - a non-zero nonce in `walletsNonces` mapping.
function requireInitiatedRecovery(address wallet) {
    require currentContract.recoveryRequests[safeContract].executeAfter > 0;
    require currentContract.walletsNonces[safeContract] > 0;
}


// The rule verifies that after recovery finalisation, the ownership of the Safe changes.
rule recoveryFinalisation(env e) {
    requireInitiatedRecovery(safeContract);

    requireInvariant reach_null();
    requireInvariant reach_invariant();
    requireInvariant inListReachable();
    requireInvariant reachableInList();
    requireInvariant ownerCountEqualsSentinelSuccessor();
    uint256 ownersLengthBefore = safeContract.getOwners().length;

    require safeContract.getThreshold() <= ownersLengthBefore;
    require ownersLengthBefore > 0;

    uint256 newOwnersCount = currentContract.recoveryRequests[safeContract].newOwners.length;

    uint256 x3;
    require x3 < newOwnersCount;
    address newOwner = currentContract.recoveryRequests[safeContract].newOwners[x3];

    finalizeRecovery(e, safeContract);
    
    address[] ownersAfter = safeContract.getOwners();
    require ownersAfter.length == newOwnersCount;
    assert safeContract.isOwner(newOwner);
}
