/*
 * Original work Copyright (c) 2017, Amirhossein Vakili, Sabria Farheen,
 *     Nancy A. Day, Ali Abbassi
 * Modified work Copyright (c) 2019, Mitchell Kember, Thi My Linh Tran,
 *     Yuezhou Gao, Nancy A. Day
 * This file is part of the TCMC-Path project, which is released under the
 * FreeBSD License. See LICENSE.txt for full license details, or visit
 * https://opensource.org/licenses/BSD-2-Clause.
 */

module ctlfc_path[S]

// ********** Kripke structure *************************************************

one sig TS {
    S0: some S,
    sigma: S -> S,
    FC: set S
}

// ********* Path definition ***************************************************

// The path is a linked list of nodes.
sig PathNode {
    // Each node has 0 or 1 successor.
    nextNode: lone PathNode,
    // Each node points to a different state.
    nodeState: disj one S
}

// The path has a start node.
one sig P0 in PathNode {}

// We can project PathNode onto the transition system.
fun pathState: S { PathNode.nodeState }
fun pathSigma: S -> S { ~nodeState.nextNode.nodeState }

fact {
    // The path respects transitions.
    pathSigma in TS.sigma
    // The start node is in an initial state.
    P0.nodeState in TS.S0
    // The path is connected.
    P0.*nextNode = PathNode
}

// Allow the user to optionally enforce a finite path.
pred finitePath {
    some p : PathNode | no p.nextNode
}

// ********** Model setup functions ********************************************

// Set by users in their model files.

fun initialState: S { TS.S0 }

fun nextState: S -> S { TS.sigma }

fun fc: S { TS.FC }

// ********** Helper functions *************************************************

private fun domainRes[R: S -> S, X: S]: S -> S { X <: R }
private fun id[X:S]: S -> S { domainRes[iden,X] }

// ********** Fair states definition *******************************************

// Fair is EcG true.
private fun Fair: S {
    let R = pathSigma |
        *R.((^R & id[S]).S & TS.FC)
}

// ********** Logical operators ************************************************

fun not_[phi: S]: S { S - phi }
fun and_[phi, si: S]: S { phi & si }
fun or_[phi, si: S]: S { phi + si }
fun imp_[phi, si: S]: S { not_[phi] + si }

// ********** Temporal operators ***********************************************

fun ex[phi: S]: S { pathSigma.(phi & Fair) }

fun ax[phi:S]: S { not_[ex[not_[phi]]] }

fun ef[phi: S]: S { (*(pathSigma)).(phi & Fair) }

fun eg[phi:S]: S {
    let R = domainRes[pathSigma, phi] |
        *R.(((^R & id[S]).S & TS.FC))
}

fun af[phi: S]: S { not_[eg[not_[phi]]] }

fun ag[phi: S]: S { not_[ef[not_[phi]]] }

fun eu[phi, si: S]: S {
    (*(domainRes[pathSigma, phi])).(si & Fair)
}

// TODO: Why was this only defined in ctlfc.als and not ctl.als?
fun au[phi, si: S]: S {
    not_[or_[eg[not_[si]],
             eu[not_[si], not_[or_[phi, si]]]]]
}

// ********** Model checking constraint ****************************************

// Called by users for model checking in their model file.
pred ctlfc_mc[phi: S] { TS.S0 in phi }
