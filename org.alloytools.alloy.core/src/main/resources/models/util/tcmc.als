/*
/*
 * Copyright (c) 2012, Amirhossein Vakili
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without 
 * modification, are permitted provided that the following conditions 
 * are met:
 *
 *    1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    2. Redistributions in binary form must reproduce the above copyright 
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

module util/tcmc[S]

//********************KRIPKE STRUCTURE DEF*************************//

one sig TS{
    S0: some S,
    sigma: S -> S,
}

//********************MODEL SET UP FUNCTIONS*************************//
// set by users in their model files

fun ks_s0: some S {TS.S0}

fun ks_sigma: S -> S {TS.sigma}

//********************HELPER FUNCTIONS*************************//

private fun bound[R: S -> S, X: S]: S -> S {X <: R}
private fun id[X:S]: S->S{bound[iden,X]}
private fun loop[R: S -> S]: S {S.(^R & id[S])}
--private fun loop[R: S -> S]: S {{a:S | (a->a) in ^R}}

//********************LOGICAL OPERATORS*************************//

fun not_ctl[phi: S]: S {S - phi}
fun and_ctl[phi, si: S]: S {phi & si}
fun or_ctl[phi, si: S]: S {phi + si}
fun imp_ctl[phi, si: S]: S {not_ctl[phi] + si}

//********************TEMPORAL OPERATORS*************************//

fun ex[phi: S]: S {TS.sigma.phi}

fun ax[phi:S]:S {not_ctl[ex[not_ctl[phi]]]}

fun ef[phi: S]: S {(*(TS.sigma)).phi }

fun eg[phi: S]: S { 
    let R= bound[TS.sigma,phi]|
    let Loop = loop[R]|
        (*R).Loop
}

fun af[phi: S]: S {not_ctl[eg[not_ctl[phi]]]}

fun ag[phi: S]: S {not_ctl[ef[not_ctl[phi]]]}

fun eu[phi, si: S]: S {(*(bound[TS.sigma, phi])).si}

fun au[phi, si: S]: S {
    not_ctl[
        or_ctl[
            eg[not_ctl[si]],
            eu[
                not_ctl[si],
                not_ctl[or_ctl[phi, si]]
            ]
        ]
    ]
}

//********************MODEL CHECKING CONSTRAINT*************************//
// called by users for mc in their model file
pred ctl_mc[phi: S]{TS.S0 in phi}
