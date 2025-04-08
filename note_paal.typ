#import "@preview/fletcher:0.5.1": node, edge, diagram
// #import "template.typ": conf
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion
#import "@preview/ctheorems:1.1.3": *
#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#import "@preview/numty:0.0.5" as nt
#set cite(form: "prose")
// Color references red
#show  ref: it => {text(fill: maroon)[#it]}

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let proof = thmproof("proof", "Proof")

#show: arkheion.with(
    title: "A note on the potential outcomes framework in continuous time",
    authors: (
        (name: "Johan Sebastian Ohlendorff", email: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen"),
    ),
    abstract: [In this brief note, we consider the target parameters of @ryalenPotentialOutcomes and compare it with the
        target parameter given in @rytgaardContinuoustimeTargetedMinimum2022, corresponding to their
        marked point process settings. It is shown that the resulting target parameters
        are the same if and only if the probability of being treated given that you go to the doctor at time $t$ is equal to 1
        for Lebesgue-almost all $t$, provided that the transition hazards for dying are strictly positive for almost all $t$.
        //From this, we conclude that the target parameters are quite different. 
    ]
    // Insert your abstract after the colon, wrapped in brackets.
    // Example: `abstract: [This is my abstract...]`
)
#set math.equation(numbering: none)


#show: thmrules.with(qed-symbol: $square$)

= Introduction

We consider a multi-state model with at most one visitation time for the treatment (that is at most one point where treatment may change), 
no time-varying covariates, and no baseline covariates. In the initial state (0) everyone starts as treated.
We consider the setting with no censoring. 
The multi-state model is shown in @fig:multi-state.
We observe the counting processes $N_t = (N^(01)_t, N^(02)_t, N^(03)_t, N^(13)_t, N^(23)_t)$
on the canonical filtered probability space $(Omega, cal(F), (cal(F)_t)_(t >= 0), P)$,
where $cal(F)_t = sigma(N_s | s <= t)$.
This means that we can represent the observed data as $O = (T_((1)), D_((1)), T_((2)))$,
where $T_((1))$ is the first event time, $D_((1)) in {01, 02, 03}$ is the first event type, $A(T_(1)) = bb(1) {D_1 != 02}$ is the treatment at the first event time, and $T_((2))$ is the second event time, possibly $oo$.
We will assume that the distribution of the jump times are continuous and that there are no jumps in common between the counting processes.
By a well-known result for marked point processes (Proposition 3.1 of @jacod1975multivariate), we know 
there exist functions $h^(i j)$, 
such that the compensators $Lambda^(i j)$ of the counting processes $N^(i j)$ with respect to $P-cal(F)_t$ are given by
$
    Lambda^(0 j) (d t) &= bb(1) {t <= T_((1))} h^(0 j) (t) d t, quad j = 1, 2, 3 \
    Lambda^(i 3) (d t) &= bb(1) {T_((1)) < t <= T_((2))} h^(i 3) (T_((1)), t) d t, quad i = 2, 3
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
    edgemsm(treat_visit, death, [$h^(13) (s, t)$])
    edgemsm(treat_visit_2, death, [$h^(23) (s, t)$])
    }

    msm_function(offset: (0,0), scale_text: 70%)
    let tint(c) = (stroke: c, fill: rgb(..c.components().slice(0,3), 5%))
    //node(label: [#align(top + right)[$P$]], enclose: ((-2.7, -0.3), (2.5, 3.3)),..tint(green))
    //msm_function(offset: (-1.5, 5), scale_text: 70%)
    //msm_function(offset: (2, 5), scale_text: 70%)
}), caption: [A multi-state model allowing one visitation time for the treatment with the possible treatment values 0/1. ])
<fig:multi-state>

= The potential outcomes framework
To follow along @ryalenPotentialOutcomes, we restrict the observations to the interval $[0, tau]$ for $tau > 0$.
We first need to define the intervention of interest,
defining the counting processes that we would have like to have observed under the intervention.
We can intervene on two components of $N$ $(N^02, N^01)$, defining the "interventional" processes as
$
    N^(g,0)_t &= 0 \
    N^(g,1)_t &= N^(01)_t + N^(02)_t \
$
This treatment regime defines that the doctor always treats the patient at the visitation time
and does not prevent the patient from visiting the doctor if they drop out of the treatment.
This thus dictates that an individual that transitioned from $0$ to $2$ should instead transition to $1$.
We define $T^(a, g)$ as the first time where the observed and the interventional process deviate.

Define also the single "intervention" process
$
    N^(g^*,0)_t = N^(g,0)_t = 0 \
$
where the interventional component is $N^02$. 
This dictates that an individual that transitioned from $0$ to $2$ should not transition to anything at that point. 
This intuitively thus means that a patient is prevented from visiting the doctor if they drop out of the treatment.
The key issue in @ryalenPotentialOutcomes is that we will not be able to differentiate between target parameters for $g$ and $g^*$.
The reason is that the likelihood under the intervention only depends on the stopping time $T^a$ and the problem that the stopping time
$T^a$ is the same under $g$ and $g^*$.

To see this, let $T^(a, g^*)$ be the first time where the observed and the interventional process (according to $g^*$) deviate.
We have
$
    T^(a, g) = inf_(t>0) {N^(g,0)_t != N^(01)_t} and inf_(t>0) {N^(g,1)_t != N^(02)_t} = inf_(t>0) {N^(g,0)_t != 0} = inf_(t>0) {N^(g^*,0)_t != 0} = T^(a, g^*)
$
Applying @thm:ryalen, we find that the target parameters are the same because the weights $W_t$ are the same under $g$ and $g^*$.
//prevents the patient from visiting the doctor if they drop out of the treatment.

//The issue in @ryalenPotentialOutcomes is that we will not be able to differentiate between $g$ and $g^*$ in the likelihood.
//The reason is that the likelihood under the intervention only depends on the stopping time $T^a$ and the problem that the stopping time
//$T^a$ is the same under $g$ and $g^*$.
//The compensator of the two counting processes are
//$
//    Lambda^(g,0) (d t) &= 0 \
//    Lambda^(g,1) (d t) &= h^(a) (t) pi_t (1) d t + h^(a) (t) (1 - pi_t (1)) d t = h^(a) (t) d t
//$

We now define the target parameter of interest in @ryalenPotentialOutcomes.
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
3. Positivity: $W_t = (bb(1) {T^A > t}) / (exp (-Lambda^02 (t))) = (1-bb(1){T_((1)) <= t, D_((1)) = a, A_((1)) = 0}) / exp(-integral_0^t bb(1) {s <= T_((1))} h^(a) (s) pi_s (0) d s)$#footnote[In the notation of @ryalenPotentialOutcomes, $tau^A = T^a$, $bb(N)_t = bb(1) {T^A <= t} = N_t^(02)$ and $ Lambda_t^(02)$ is the compensator of this process.]
   is a uniformly integrable martingale or equivalently that $R^"Pål"$ given by $d R^"Pål" = W_tau d P$ is a probability measure.
    
   Then the estimand of interest $Psi_t^"Ryalen": cal(M) -> RR_+$ is identifiable by
$
    Psi_t^"Ryalen" (P) := bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t] = bb(E)_(R^"Pål") [Y_t]
$
] <thm:ryalen>

From this, we can derive an alternate representation of the target parameter. We have that 
$
    Psi_t^"Ryalen" (P) &= bb(E)_P [Y_t W_t] \
        &= bb(E)_P [ bb(1) {T_((1)) <= t} Y_t W_t] + bb(E)_P [bb(1) {T_((2)) <= t} Y_t W_t] \
        &= bb(E)_P [ bb(1) {T_((1)) <= t} Y_t (1-bb(1) {T^a > t})/exp(-integral_0^(T_((1))) h^02 (s) d s)] + bb(E)_P [bb(1) {T_((2)) <= t} Y_t (1-bb(1) {T^a > t})/exp(-integral_0^(T_((1))) h^02 (s) d s)] \
        &= bb(E)_P [ bb(1) {T_((1)) <= t, D_((1)) = 03} 1/exp(-integral_0^(T_((1))) h^02 (s) d s)] + bb(E)_P [bb(1) {T_((2)) <= t} (1-N_t^02 )/exp(-integral_0^(T_((1))) h^02 (s) d s)] \
        &= bb(E)_P [ bb(1) {T_((1)) <= t, D_((1)) = 03} 1/exp(-integral_0^(T_((1))) h^02 (s) d s)] + bb(E)_P [bb(1) {T_((2)) <= t, D_((1)) = 01} 1/exp(-integral_0^(T_((1))) h^02 (s) d s)] \
        &= integral_0^t 1/exp(-integral_0^(t) h^02 (s) d s) exp( - sum_j integral_0^s h^(0 j) (u) d u) h^03 (s) d s \
        &+ integral_0^t 1/exp(-integral_0^(t) h^02 (s) d s) exp( - sum_j integral_0^s h^(0 j) (u) d u) (integral_s^t exp( - integral_s^w h^(1 3) (s, u) d u) h^13 (s, w) d w) h^01 (s) d s \
        &= integral_0^t exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u) h^03 (s) d s \
        &+ integral_0^t exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u) (integral_s^t exp( - integral_s^w h^(1 3) (s, u) d u) h^13 (s, w) d w) h^01 (s) d s \
$

== The target parameter in @rytgaardContinuoustimeTargetedMinimum2022

To discuss @rytgaardContinuoustimeTargetedMinimum2022, additionally define
$
    Lambda^(a) (t) &= (h^(01) (t) + h^(02) (t)) bb(1) {T_((1)) <= t} \
    pi_t (1) &= (h^(01) (t))/(h^(01) (t) + h^(02) (t)) 
$
Here, we can interpret $Lambda^(a) (t)$ as the intensity of the visitation times and $pi_t (1)$ as the probability of being treated given that you go to the doctor at time $t$.
Here $Lambda^a (t)$ is the compensator of the counting process $N_t^a = N^(01)_t + N^(02)_t$ with respect to $P-cal(F)_t$.
Furthermore, let $N_t^d = N^(03)_t + N^(13)_t + N^(23)_t$ be the counting process for the event of interest.
Then, its compensator is given by
$
    Lambda^d (d t) &= bb(1) {t <= T_((1))} h^(03) (t) d t \
        &+ bb(1) {T_((1)) < t <= T_((2))} (bb(1) {D_((1)) = 01}h^(13) (T_((1)), t) + bb(1) {D_((1)) = 02} h^(23) (T_((1)), t)) d t
$
Furthermore, let $A (t) = bb(1) {T_((1)) > t} + bb(1) {T_((1)) <= t, D_((1)) != 02}$ be the treatment process at time $t$.
@rytgaardContinuoustimeTargetedMinimum2022 give their likelihood as
$
    d P (O) &= prodint(t, 0, tau) (d Lambda^a (t) (pi_t (1))^(bb(1) {A(t)=1}) (1-pi_t (1))^(bb(1) {A(t)=0}) )^(Delta N^a (t)) (1 - d Lambda^a (t))^(1 - N^a (d t)) \
        &times prodint(t, 0, tau) (d Lambda^d (t)  )^(Delta N^d (t)) (1 - d Lambda^d (t))^(1 - N^d (d t)) \
        &= prodint(t, 0, tau) ((pi_t (1))^(bb(1) {A(t)=1}) (1-pi_t (1))^(bb(1) {A(t)=0}) )^(Delta N^a (t)) \
        &times prodint(t, 0, tau) (d Lambda^a (t))^(Delta N^a (t)) (1 - d Lambda^a (t))^(1 - N^a (d t)) (d Lambda^d (t)  )^(Delta N^d (t)) (1 - d Lambda^d (t))^(1 - N^d (d t)) \
        &= prodint(t, 0, tau) d G_t d Q_t 
$
where
$
    d G_t = ((pi_t (1))^(bb(1) {A(t)=1}) (1-pi_t (1))^(bb(1) {A(t)=0}) )^(N^a (d t)) \
    d Q_t = (d Lambda^a (t))^(N^a (d t)) (1 - d Lambda^a (t))^(1 - N^a (d t)) (d Lambda^d (t)  )^(N^d (d t)) (1 - d Lambda^d (t))^(1 - N^d (d t)) \
$
Let $d G^*_t = ((1)^(bb(1) {A(t)=1}) (0)^(bb(1) {A(t)=0}) )^(N^a (d t)) = ((0)^(bb(1) {A(t)=0}))^(N^a (d t))$.
Then define the likelihood as
$
    d P_(Q, G^*) (O) &= prodint(t, 0, tau) d G^*_t d Q_t 

$
and their target estimand $Psi_t^("Rytgaard") : cal(M) -> RR_+$ as
$
    Psi_t^("Rytgaard") (P) = mean(P_(Q, G^*)) [N^d_tau] = P_(Q, G^*) (T_((1)) <= tau, D_((1)) = 03) + P_(Q, G^*) (T_((2)) <= tau) \
    //integral_(cal(O)) y prodint(t, 0, tau) d G^*_t d Q_t 
$
//where $cal(O)$ indicates that we integrate over the observed data and $y$ outcome at time $tau$.

Let us calculate the density $d P_(Q, G^*) (O)$ restricted to $history(1) = (T_((1)), D_((1)))$ and $history(2) = (T_((1)), D_((1)), T_((2)))$ (further restricted to $T_((2)) < oo$).
To get a fully rigorous result, consider Proposition 1 in @ryalenPotentialOutcomes and Theorem 8.1.2 in @last1995marked.

//Calculate $mean(P) [d P_(Q, G^*) (O) bb(1) {T_1 < T_2 < oo} | history(2)]$.
We have
$
     prodint(t, 0, tau) d G^*_t d Q_t = prodint(t, 0, t_((1))) d G^*_t d Q_t prodint(t, t_((1)), tau) d G^*_t d Q_t
$
Since $integral_((0, tau]) prodint(t, t_((1)), tau) d G^*_t d Q_t bb(1) {t_1 < t_2} = 1$ ($prodint(t, t_((1)), tau) d G^*_t d Q_t$ is the conditional density of $t_2$ given $(t_1,d_1)$ integrated over $t_2$; in the case where $d_1 = 03$ (death initially occurs), we define this integral as 1),
we get $P_(Q, G^*) (T_((1)) in d t_1, D_((1)) = d_1)$ by
$
    prodint(t, 0, t_((1))) d G^*_t d Q_t &=  ((0)^(bb(1) {d_1 = 02}))^(bb(1) {d_1 in {01,02}}) \
        &times  (d Lambda^a (t_1))^(bb(1) {d_1 in {01, 02}}) (d Lambda^d (t_1)  )^(bb(1) {d_1 = 03}) prodint(t, 0, t_((1))) (1 - d Lambda^d (t)) (1 - d Lambda^a (t))\
        &=  (d Lambda^a (t_1))^(bb(1) {d_1 in {01}}) (0 d t_1)^(bb(1) {d_1 in {02}})  (d Lambda^d (t_1)  )^(bb(1) {d_1 = 03}) prodint(t, 0, t_((1))) (1 - d (Lambda^d (t) + Lambda^a (t)))\
        &=  ((h^01 (t_1)+h^02 (t_1)) d t_1)^(bb(1) {d_1 in {01}}) (0 d t_1)^(bb(1) {d_1 in {02}})  (h^03 (t_1) d t_1)^(bb(1) {d_1 = 03}) prodint(t, 0, t_((1))) (1 - sum_j h^(0 j) (t) d t)\
        &=  prodint(t, 0, t_((1))) (1 - sum_j h^(0 j) (t) d t) bb(1) {d_1 = 01} (h^01 (t_1) + h^02 (t_1)) d t_1 \
        &+  prodint(t, 0, t_((1))) (1 - sum_j h^(0 j) (t) d t) bb(1) {d_1 = 03} h^03 (t_1) d t_1 
$
(compare with Equation (11) in @ryalenPotentialOutcomes).
Similarly, we may find $P_(Q, G^*) (T_((1)), D_((1)), T_((2)) in (d t_1, d_1, d t_2))$ on $T_2 < oo$ given by
$
    &prodint(t, 0, t_((1))) d G^*_t d Q_t prodint(t, t_((1)), t_((2))) d G^*_t d Q_t bb(1) {t_1 < t_2 } \
        &= bb(1) {t_1 < t_2}  prodint(t, 0, t_((1))) (1 - sum_j h^(0 j) (t) d t) bb(1) {d_1 = 01} (h^01 (t_1) + h^02 (t_1)) \
        &#h(1cm) times prodint(t, t_((1)), t_((2))) (1 - h^13 (t_1, t) d t) h^(13) (t_1, t_2) d t_2 d t_1 \
$

// To that end, we have that 
// $
//     &P((T_((1)), D_((1)), T_((2))) in A times B times C, T_((2)) < oo) \
//         &= integral_A prodint2(u, 0, s) (1 - sum_(j) h^(0 j) (u) d u) \
//         &times (sum_(j in B) h^(0 j) (s) ((integral_C bb(1) {s < w} prodint2(u, s, w) (1 - h^(j 3) (s) d s) h^(j 3) (w) d w) bb(1) {j != 3})) d s \
//         &= integral_A prodint2(u, 0, s) (1 - (Lambda^a (s, 0) + Lambda^d (s, 0)) d u) \
//         &times (sum_(j in B) (bb(1) {j = 01} pi_s (1) Lambda^(a) (d s, 0) ((integral_C bb(1) {s < w} prodint2(u, s, w) (1 - h^(j 3) (s) d s) h^(j 3) (w) d w) bb(1) {j != 3} + bb(1) {oo in C, j = 3})) d s
// $
Then for the target estimand, we have
$
    Psi_tau^("Rytgaard") (P) &= P_(Q, G^*) (T_((1)) <= tau, D_((1)) = 03) + P_(Q, G^*) (T_((2)) <= tau) \
        &=integral_0^tau exp( - sum_(j) integral_0^s h^(0 j) (u) d u) h^03 (s) d s \
        &+ integral_0^tau exp( - sum_(j) integral_0^s h^(0 j) (u) d u) (integral_s^tau exp( - integral_s^w h^(1 3) (s, u) d u) h^13 d w ) (h^01 (s) +h^02 (s)) d s 
$

== Comparison of the approaches

We are now in a position, where we can readily compare the approaches in @rytgaardContinuoustimeTargetedMinimum2022 and
@ryalenPotentialOutcomes. //The observational parameter of interest is identifiable by //Let $N_t = (N^(y)_t, N^(a)_t, N^(03)_t, N^(13)_t, N^(23)_t)$ be the multivariate counting process of the multi-state model.

//and let $N_t^(bullet) = N^(01)_t + N^(02)_t + N^(03)_t + N^(13)_t + N^(23)_t$ count the total number of events. 
//Given any measurable set $A$ we have there exists sets $B_0, B_1, B_2$ such that

Suppose that $h^02 (s) > 0$ and $h^13 (s, w) > 0$ for Lebesgue almost all $s, w$.
From this, we conclude that $Psi^("Rytgaard")_t (P) = Psi_t^"Ryalen" (P)$ if and only if $h^02 equiv 0$ a.e. if and only if $pi_t (1) equiv 1$ a.e.
To see this, note that
$
    Psi_t^"Ryalen" (P)- Psi^("Rytgaard")_t (P) &= integral_0^t exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u)(1-exp( - integral_0^s h^02 (u) d u)) h^03 (s) d s \
        &+ integral_0^t exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u) (integral_s^t exp( - integral_s^w h^(1 3) (s, u) d u) h^13 d w ) \
        &#h(3cm) times(1-exp( - integral_0^s h^02 (u) d u)) h^01 (s) d s \
        &+integral_0^t exp( - sum_(j) integral_0^s h^(0 j) (u) d u) (integral_s^t exp( - integral_s^w h^(1 3) (s, u) d u) h^13 d w ) h^02 (s) d s \
$
Since each term is non-negative, $Psi^("Rytgaard")_t (P) = Psi_t^"Ryalen" (P)$ implies that each term is equal to zero.
Since each of the integrands are non-negative, we must have that the integrands are equal to zero for Lebesgue almost all $t > 0$, i.e.,
for the first term we see that and letting $m$ denote the Lebesgue measure, we have
$
    exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u)(1-exp( - integral_0^s h^02 (u) d u)) h^03 (s) = 0 quad m-"a.e." &<=> \
        (1-exp( - integral_0^s h^02 (u) d u)) h^03 (s) = 0 quad m-"a.e." &<=> \
        (1-exp( - integral_0^s h^02 (u) d u)) = 0 quad m-"a.e." &<=> \
        h^02 (s) = 0 quad  m-"a.e."
$
with similar arguments for the second and third terms. 
= Does the g-formula in @rytgaardContinuoustimeTargetedMinimum2022 have a causal interpretation? 

We now consider the question concerning whether there is a causal interpretation of the g-formula in @rytgaardContinuoustimeTargetedMinimum2022.
Given $W_t^*$ as in the next theorem, we can calculate that, $bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t^*] = Psi_t^("Rytgaard") (P)$.

A simple result is given in the following theorem. Note that we can also formulated the exchangeability condition for each $t$ separately
instead of formulating stochastic process conditions. 

#theorem[
    We suppose that there exists a potential outcome process $(tilde(Y)_t)_(t in [0,tau])$ such that

1. Consistency: $tilde(Y)_t bb(1) {T^A > t} = Y_t bb(1) {T^A > t}$ for all $t > 0$ $P$-a.s.
2. Exchangeability: We have
   $
       (tilde(Y)_t)_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)) 
   $
3. Positivity: The measure given by $d R^"Helene" = W d P$ where $W^*_t = ((bb(1) {A(T_((1))) = 1}) / (pi_(T_(1)) (1)))^(N_t^01 +N^02_t)$ is a probability measure.

Then the estimand of interest is identifiable by
$
    bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t] = bb(E)_(R^"Helene") [Y_t]
$
]
#proof[
    Write $tilde(Y)_t = bb(1) {t < T_((1))} tilde(Y)_t + bb(1) {T_((1)) <= t} tilde(Y)_t$
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
        bb(E)_P [ bb(1) {T_((1)) <= t} Y_t W_t] &= bb(E)_P [ bb(1) {T_((1)) <= t} bb(1) {T^a > t} Y_t W_t] \
            &=bb(E)_P [ bb(1) {T_((1)) <= t} bb(1) {T^a > t} tilde(Y)_t W_t] \
            &=bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t W_t] \
            &=bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
            &=bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t | A(T_((1))), D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
            &=bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t | D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
            &=bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t | D_1, T_1] bb(E)_P [((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a}) | T_1, D_1]] \
            &= bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t | D_1, T_1] ] \
            &= bb(E)_P [  bb(1) {T_((1)) <= t} tilde(Y)_t ]
    $
    which suffices to show the claim.
]

With more than two events, though, the exchangeability condition becomes more difficult to interpret.
In the case with at most three events, for the previous argument to go through, we would need the three exchangeability conditions
$
    (tilde(Y)_t bb(1) {T_((1)) <= t < T_((2))})_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)), \
    (tilde(Y)_t bb(1) {T_((2)) <= t})_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)), \
    (tilde(Y)_t)_(t in [0,tau]) perp A(T_((2))) | T_((2)), D_((2)), A(T_((1))), T_((1)), D_((1)), \
$
It would be interesting to see if there are some explicit conditions such that
$
    (tilde(Y)_t)_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)) 
$
implies the two first exchangeability conditions. An obvious one is if the event times are independent of the treatment given the history
which is unlikely to hold.

The next theorem gives a different causal interpretation of the g-formula in @rytgaardContinuoustimeTargetedMinimum2022.
Unlike the previous theorem, the exchangeability wont have to be specified in terms of $tilde(Y)_t$ multiplied by a stochastic indicator function
if there are more than two events. This issue is however that we are assuming the existence of multiple potential outcome processes and not just one.

#theorem[
    We suppose that there exists two potential outcome process $(tilde(Y)_(t,1))_(t in [0,tau])$ and $(tilde(Y)_(t,2))_(t in [0,tau])$ such that
    these are potential outcomes of $Y_(t,1) = N^(03)_t$ and $Y_(t,2) = N^(13)_t+N^(23)_t$, respectively (the potential outcomes for each possible event where the outcome can occur).
    Then we obviously define that
    $tilde(Y)_t = tilde(Y)_(t,1) + tilde(Y)_(t,2)$ and $Y_t = Y_(t,1) + Y_(t,2)$.

    1. Consistency: $tilde(Y)_(t,i) bb(1) {T^A > t} = Y_(t,i) bb(1) {T^A > t}$ for all $t > 0$ $P$-a.s for $i = 1, 2$.
2. Exchangeability: We have
   $
       (tilde(Y)_(t,i))_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)) 
   $
   for $i = 1, 2$.
3. Positivity: The measure given by $d R^"Helene" = W d P$ where $W_t = ((bb(1) {A(T_((1))) = 1}) / (pi_(T_(1)) (1)))^(N_t^01 +N^02_t)$ is a probability measure.

Then the estimand of interest is identifiable by
$
    bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t] = bb(E)_(R^"Helene") [Y_t]
$
]
#proof[
    Now, we see immediately that
    $
        bb(E)_P [ Y_(t,1) W_t ] &= bb(E)_P [ tilde(Y)_(t,1) ]
    $
    because $tilde(Y)_(t,1)$ is always $Y_(t,1)$.
    On the other hand, we have that
    $
        bb(E)_P [  Y_(t,2) W_t ] &=  bb(E)_P [  Y_(t,2) ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a}) ]\
            &=bb(E)_P [  tilde(Y)_(t,2) ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
            &=bb(E)_P [ bb(E)_P [ tilde(Y)_(t,2) | A(T_((1))), D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
            &=bb(E)_P [ bb(E)_P [ tilde(Y)_(t,2) | D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
            &=bb(E)_P [ bb(E)_P [ tilde(Y)_(t,2) | D_1, T_1] bb(E)_P [((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a}) | T_1, D_1]] \
            &= bb(E)_P [ bb(E)_P [ tilde(Y)_(t,2) | D_1, T_1] ] \
            &= bb(E)_P [  tilde(Y)_(t,2) ]
    $
    which suffices to show the claim.
]

#bibliography("references/ref.bib",style: "apa")
