#import "@preview/fletcher:0.5.1": node, edge, diagram
// #import "template.typ": conf
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
#import "@preview/cetz:0.3.1"
#import "@preview/ctheorems:1.1.3": *
#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#import "@preview/numty:0.0.5" as nt
#show: thmrules
#set cite(form: "prose")
#set heading(numbering: "1.")

// Color references red
#show  ref: it => {text(fill: maroon)[#it]}
#let mapsto = $arrow.bar$
#let scr(it) = text(
    features: ("ss01",),
    box($cal(it)$),
)

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let proof = thmproof("proof", "Proof")

#show: arkheion.with(
    title: "A note on the potential outcomes framework in continuous time",
    authors: (
        (name: "Johan Sebastian Ohlendorff", email: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen"),
    ),
    abstract: [In this brief note, we consider the seminal work by @ryalenPotentialOutcomes and compare it with the
        approach given in @rytgaardContinuoustimeTargetedMinimum2022, corresponding to their
        marked point process settings. We study these works in simple multi-state models.
    ]
    // Insert your abstract after the colon, wrapped in brackets.
    // Example: `abstract: [This is my abstract...]`
)

#show: thmrules.with(qed-symbol: $square$)

= Introduction

We consider a multi-state model with at most one visitation time for the treatment (that is at most one point where treatment may change), 
no time-varying covariates, and no baseline covariates. In the initial state (0) everyone starts as treated.
We consider the setting with no censoring. 
The multi-state model is shown in @fig:multi-state.
We observe the counting processes $N_t = (N^(01)_t, N^(02)_t, N^(03)_t, N^(13)_t, N^(23)_t)$
on the canonical filtered probability space $(Omega, cal(F), (cal(F)_t)_(t >= 0), P)$,
where $cal(F)_t = sigma(N_s | s <= t)$.
This means that we can represent the observed data as $O = (T_((1)), D_((1)), A(T_((1))), T_((2)))$,
where $T_((1))$ is the first event time, $D_((1)) in {01, 02, 03}$ is the first event type, $A(T_(1)) in {0, 1}$ is the treatment at the first event time, and $T_(2)$ is the second event time, possibly $oo$.
We will assume that the distribution of the jump times are continuous and that there are no jumps in common between the counting processes.
By a well-known result for marked point processes (Proposition 3.1 of @jacod1975multivariate), we know 
there exist functions $h^(i j): RR_+ -> RR_+$
such that the compensators $Lambda^(i j)$ of the counting processes $N^(i j)$ with respect to $P-cal(F)_t$ are given by
$
    Lambda^(0 j) (d t) &= bb(1) {t <= T_((1))} h^(0 j) (t) d t, quad j = 1, 2, 3 \
    Lambda^(i 3) (d t) &= bb(1) {T_((1)) < t <= T_((2))} h^(i 3) (t) d t, quad i = 2, 3
$

//As always, we will assume finite-variation martingales in the below, so that our underlying assumption that the counting proceses have no jumps in common implies that the martingales are orthogonal).

#figure(diagram(spacing: (5mm, 4.5mm), debug: false, node-stroke: 0.5pt, node-inset: 10pt, label-size: 7pt, {
    

    let msm_function(offset: (0,0), scale_text: 70%) = {
        let (novisit, treat_visit, treat_visit_2, death) = (
            nt.add((0,0),offset)
            , nt.add((-1.5,1.5),offset)
            , nt.add((1.5,1.5),offset)
            , nt.add((0, 3),offset))
        
    node(novisit, [#scale(scale_text)[$A(0)=1$ (0)]])
    node(treat_visit, [#scale(scale_text)[patient visit (1) \ stay on treatment]])
        node(treat_visit_2, [#scale(scale_text)[patient visit (2) \ drop treatment]])
        node(death, [#scale(scale_text)[Death (3)]])
    edgemsm(novisit, treat_visit, [$h^(01) (t)$])
    edgemsm(novisit, treat_visit_2, [$h^(02) (t)$])
    
    edgemsm(novisit, death, [$h^(03) (t)$])
    edgemsm(treat_visit, death, [$h^(13) (t)$])
    edgemsm(treat_visit_2, death, [$h^(23) (t)$])
    }

    msm_function(offset: (0,0), scale_text: 70%)
    let tint(c) = (stroke: c, fill: rgb(..c.components().slice(0,3), 5%))
    //node(label: [#align(top + right)[$P$]], enclose: ((-2.7, -0.3), (2.5, 3.3)),..tint(green))
    //msm_function(offset: (-1.5, 5), scale_text: 70%)
    //msm_function(offset: (2, 5), scale_text: 70%)
}), caption: [A multi-state model allowing one visitation time for the treatment with the possible treatment values 0/1. ])
<fig:multi-state>
Define
$
    Lambda^(a) (t) &= (h^(01) (t) + h^(02) (t)) bb(1) {T_((1)) <= t} \
    pi_t (1) &= (h^(01) (t))/(h^(01) (t) + h^(02) (t)) 
$
Here, we can interpret $Lambda^(a) (t)$ as the intensity of the visitation times and $pi_t (1)$ as the probability of being treated given that you go to the doctor at time $t$.
We will represent the observations from such a multi-state model as a marked point process.

= The potential outcomes framework
To follow along @ryalenPotentialOutcomes, we restrict the observations to the interval $[0, tau]$ for $tau > 0$.
For this, we need to define the intervention of interest,
defining the counting processes that we would have like to have observed under the intervention.
For this define the corresponding "interventional" processes as
$
    N^(g,0)_t &= 0 \
    N^(g,1)_t &= N^(01)_t + N^(02)_t \
$
instead of $N^(01)_t$, $N^(02)_t$. This treatment regime defines that the doctor always treats the patient at the visitation time
and does not prevent the patient from visiting the doctor if they drop out of the treatment.
In contrast, the single "intervention" process
$
    N^(g^*,0)_t &= 0 \
$
prevents the patient from visiting the doctor if they drop out of the treatment.
//The compensator of the two counting processes are
//$
//    Lambda^(g,0) (d t) &= 0 \
//    Lambda^(g,1) (d t) &= h^(a) (t) pi_t (1) d t + h^(a) (t) (1 - pi_t (1)) d t = h^(a) (t) d t
//$
We let $T^a = inf_(t>0) {N^(g,0)_t != N^(01)_t} and inf_(t>0) {N^(g,1)_t != N^(02)_t} = inf_(t>0) {N^(g,0)_t != 0}$.
The outcome of interest is death at time $t$, i.e., 
$
    Y_t = N^(13)_t + N^(03)_t + N^(23)_t = bb(1) {T_1 <= t, D_1 = y} + bb(1) {T_2 <= t}
$
and we want to estimate $bb(E)_P [tilde(Y)_t]$ where $tilde(Y)_t$ denotes the outcome at time $t$, had the treatment regime (staying on treatment), possibly contrary to fact, been followed.

#theorem([Theorem 1 of @ryalenPotentialOutcomes])[
    We suppose that there exists a potential outcome process $(tilde(Y)_t)_(t in [0,tau])$ such that

1. Consistency: $tilde(Y)_t bb(1) {T^A > t} = Y_t bb(1) {T^A > t}$ for all $t > 0$ $P$-a.s.
2. Exchangeability: The $P-cal(F)_t$ compensators 
   $Lambda^(01)$, $Lambda^(02)$ are also compensators for $cal(G)_t=cal(F)_t or sigma(tilde(Y)_s, tau >= s >= 0)$.
   Here $tilde(Y)_s$ is added at baseline, so that $cal(G)_0 = sigma(tilde(Y)_s, tau >= s >= 0)$.
    3. Positivity: $W_t = (bb(1) {T^A > t}) / exp(-Lambda_t^02) = (1-bb(1){T_((1)) <= t, D_((1)) = a, A_((1)) = 0}) / exp(-integral_0^t bb(1) {s <= T_((1))} h^(a) (s) pi_s (0) d s)$
   is a uniformly integrable martingale or equivalently that $R^"Pål"$ given by $d R^"Pål" = W_tau d P$ be a probability measure.

Then the estimand of interest is identifiable by
$
    bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t] = bb(E)_(R^"Pål") [Y_t]
$
]

We are now in a position, where we can readily compare the approaches in @rytgaardContinuoustimeTargetedMinimum2022 and
@ryalenPotentialOutcomes. Generally speaking the likelihood factorizes as,
by the orthogonal martingale assumption, 
$
    d "P" &= exp(- Lambda^01 (d t) - Lambda^02 (d t) - Lambda^03 (d t)) (Lambda^01 (d t))^(N^01 (d t)) (Lambda^02 (d t))^(N^02 (d t)) (Lambda^03 (d t))^(N^03 (d t)) \
        &times exp(- Lambda^13 (d t)) (Lambda^(13) (d t))^(N^(13) (d t)) times exp(- Lambda^23 (d t)) (Lambda^(23) (d t))^(N^(23) (d t)) \
        &= exp(-Lambda^03 (d t) - Lambda^a (d t)) (pi_(t) (1) Lambda^a (d t))^(N^(01) (d t)) ((1-pi_(t) (1)) Lambda^a (d t))^(N^(02) (d t)) (Lambda^03 (d t))^(N^03 (d t)) \
        &times exp(- Lambda^13 (d t)) (Lambda^(13) (d t))^(N^(13) (d t)) times exp(- Lambda^23 (d t)) (Lambda^(23) (d t))^(N^(23) (d t)) \
        &= exp(-Lambda^03 (d t)-Lambda^a (d t)) (Lambda^03 (d t))^(N^03 (d t)) exp(- Lambda^13 (d t)) (Lambda^(13) (d t))^(N^(13) (d t)) times exp(- Lambda^23 (d t)) (Lambda^(23) (d t))^(N^(23) (d t)) \
        &(Lambda^a (d t))^(N^(01) (d t)) ((1-pi_(t) (1)))^(N^(02) (d t)) times (pi_(t) (1))^(N^(01) (d t)) ((1-pi_(t) (1)))^(N^(02) (d t)) \
        &= d Q times d G
$
where
$
    d Q &= exp(-Lambda^03 (d t)) (Lambda^03 (d t))^(N^03 (d t)) exp(- Lambda^13 (d t)) (Lambda^(13) (d t))^(N^(13) (d t)) times exp(- Lambda^23 (d t)) (Lambda^(23) (d t))^(N^(23) (d t))\
        & times exp(-Lambda^a (d t)) (Lambda^a (d t))^(N^(01) (d t)) ((1-pi_(t) (1)))^(N^(02) (d t)) \
    d G &= (pi_(t) (1) )^(N^(01) (d t)) ((1-pi_(t) (1)) )^(N^(02) (d t)) 
$
@rytgaardContinuoustimeTargetedMinimum2022 define their target estimand as $bb(E)_(R^"Helene") [Y_t]$, where
$
    d "R"^"Helene" &= d Q (d t) times d G^* (d t)
$
where
$
    d G^* (d t) = (1)^(N^(01) (d t)) (0)^(N^(02) (d t)) \
$
In contrast, in @ryalenPotentialOutcomes, we have that, by simple multiplication,
$
    d "R"^"Pål" &= W (d t) d "P" =
    exp(-Lambda^03 (d t)) (Lambda^03 (d t))^(N^03 (d t)) exp(- Lambda^13 (d t)) (Lambda^(13) (d t))^(N^(13) (d t)) times exp(- Lambda^23 (d t)) (Lambda^(23) (d t))^(N^(23) (d t)) \
        &times exp(- pi_(t) (1) Lambda^a (d t)) (pi_(t) (1) Lambda^a (d t))^(N^(01) (d t)) (0)^(N^(02) (d t)) \
$
which does not factorize into $Q$ and $G$-part of the likelihood. 
This argument may be made more rigorous by applying Theorem 3 of @ryalenPotentialOutcomes,
finding the compensators in the reweighted measure $d R^"Pål"$.

= Does the g-formula in @rytgaardContinuoustimeTargetedMinimum2022 have a causal interpretation? 

We now consider the question concerning whether there is a causal interpretation of the g-formula in @rytgaardContinuoustimeTargetedMinimum2022.
A simple result is given in the following theorem.
It would be interesting to see if there are some explicit conditions such that
$
    (tilde(Y)_t)_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)) 
$
implies the exchangeability condition.
An obvious one is if the event times are independent of the treatment given the history
which is unlikely to hold. Note that we can also formulated the exchangeability condition for each $t$ separately.

#theorem[
    We suppose that there exists a potential outcome process $(tilde(Y)_t)_(t in [0,tau])$ such that

1. Consistency: $tilde(Y)_t bb(1) {T^A > t} = Y_t bb(1) {T^A > t}$ for all $t > 0$ $P$-a.s.
2. Exchangeability: We have
   $
       (tilde(Y)_t bb(1) {T_((1)) <= t < T_((2))))_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)) \
       (tilde(Y)_t bb(1) {T_((2)) <= t))_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1))
   $
3. Positivity: The measure given by $d R^"Helene" = W d P$ where $W_t = ((bb(1) {A(T_((1))) = 1}) / (pi_(T_(1)) (1)))^(N_t^01 +N^02_t)$ is a probability measure.

Then the estimand of interest is identifiable by
$
    bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t] = bb(E)_(R^"Helene") [Y_t]
$
]
#proof[
    Write $tilde(Y)_t = bb(1) {t < T_((1))} tilde(Y)_t + bb(1) {T_((1)) <= t < T_((2))} tilde(Y)_t + bb(1) {T_((2)) <= t} tilde(Y)_t$.
    Now, we see immediately that
    $
        bb(E)_P [ bb(1) {t < T_((1))} tilde(Y)_t] &= bb(E)_P [ bb(1) {t < T_((1))} tilde(Y)_t bb(1) {T^a > t}] \
            &= bb(E)_P [ bb(1) {t < T_((1))} Y_t bb(1) {T^a > t}] \
            &= bb(E)_P [ bb(1) {t < T_((1))} Y_t] \
            &= bb(E)_P [ bb(1) {t < T_((1))} Y_t W_t] \
    $
    since $T^a$ must be $T_((1))$ if finite.  
    On the other hand, we have that
    $
        bb(E)_P [ bb(1) {T_((1)) <= t < T_((2))} Y_t W_t] &= bb(E)_P [ bb(1) {T_((1)) <= t < T_((2))} bb(1) {T^a > t} Y_t W_t] \
            &=bb(E)_P [ bb(1) {T_((1)) <= t < T_((2))} bb(1) {T^a > t} tilde(Y)_t W_t] \
            &=bb(E)_P [ bb(1) {T_((1)) <= t < T_((2))} tilde(Y)_t W_t] \
            &=bb(E)_P [ bb(1) {T_((1)) <= t < T_((2))} tilde(Y)_t ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
            &=bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t < T_((2))} tilde(Y)_t | A(T_((1))), D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
            &=bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t < T_((2))} tilde(Y)_t | D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
            &=bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t < T_((2))} tilde(Y)_t | D_1, T_1] bb(E)_P [((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a}) | T_1, D_1]] \
            &= bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t < T_((2))} tilde(Y)_t | D_1, T_1] ] \
            &= bb(E)_P [  bb(1) {T_((1)) <= t < T_((2))} tilde(Y)_t ]
    $
    By the same calculations, we have that
    $
    bb(E)_P [ bb(1) {T_((2)) <= t} Y_t W_t] = bb(E)_P [ bb(1) {T_((2)) <= t} tilde(Y)_t ]
    $
    which suffices to show the claim.
] 

#bibliography("references/ref.bib",style: "apa")
