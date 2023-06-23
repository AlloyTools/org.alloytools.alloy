/*
 * Original work Copyright (c) 2017, Amirhossein Vakili, Sabria Farheen,
 *     Nancy A. Day, Ali Abbassi
 * Modified work Copyright (c) 2019, Mitchell Kember, Thi My Linh Tran,
 *     Yuezhou Gao, Nancy A. Day
 * This file is part of the TCMC-Path project, which is released under the
 * FreeBSD License. See LICENSE.txt for full license details, or visit
 * https://opensource.org/licenses/BSD-2-Clause.
 */

module tcmcfc[S]

// ********** Kripke structure *************************************************

one sig TS {
    S0: some S,
    sigma: S -> S,
    FC: set S
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
    let R = TS.sigma |
        *R.((^R & id[S]).S & TS.FC)
}

// ********** Logical operators ************************************************

fun not_[phi: S]: S { S - phi }
fun and_[phi, si: S]: S { phi & si }
fun or_[phi, si: S]: S { phi + si }
fun imp_[phi, si: S]: S { not_[phi] + si }

// ********** Temporal operators ***********************************************

fun ex[phi: S]: S { TS.sigma.(phi & Fair) }

fun ax[phi:S]: S { not_[ex[not_[phi]]] }

fun ef[phi: S]: S { (*(TS.sigma)).(phi & Fair) }

fun eg[phi:S]: S {
    let R = domainRes[TS.sigma, phi] |
        *R.(((^R & id[S]).S & TS.FC))
}

fun af[phi: S]: S { not_[eg[not_[phi]]] }

fun ag[phi: S]: S { not_[ef[not_[phi]]] }

fun eu[phi, si: S]: S {
    (*(domainRes[TS.sigma, phi])).(si & Fair)
}

// TODO: Why was this only defined in ctlfc.als and not ctl.als?
fun au[phi, si: S]: S {
    not_[or_[eg[not_[si]],
             eu[not_[si], not_[or_[phi, si]]]]]
}

// ********** Model checking constraint ****************************************

// Called by users for model checking in their model file.
pred ctlfc_mc[phi: S] { TS.S0 in phi }
