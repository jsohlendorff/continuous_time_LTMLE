#import "@preview/fletcher:0.5.1": node, edge, diagram
// #import "template.typ": conf
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
#import "@preview/cetz:0.3.1"
#set cite(form: "prose")
// Color references red
#show  ref: it => {text(fill: maroon)[#it]}

#let scr(it) = text(
    features: ("ss01",),
    box($cal(it)$),
)

#show: arkheion.with(
    title: "A note on the potential outcomes framework in continuous time",
    authors: (
        (name: "Johan Sebastian Ohlendorff", email: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen"),
    ),
    abstract: [In this brief note, we consider the seminal work by @ryalenPotentialOutcomes and compare it with the
        approach given in @rytgaardContinuoustimeTargetedMinimum2022, corresponding to their
        marked point process settings. We study these works in simple multi-state models. ]
    // Insert your abstract after the colon, wrapped in brackets.
    // Example: `abstract: [This is my abstract...]`
)


#show: thmrules.with(qed-symbol: $square$)

We consider a multi-state model with states ${0, 1, 2, 3}$ with at most one visitation time for the treatment (that is at most one point where treatment may change), 
no time-varying covariates, and no baseline covariates. In the initial state everyone starts as treated. We consider the setting with no censoring. 
The multi-state model is shown in @fig:multi-state. 
//As always, we will assume finite-variation martingales in the below, so that our underlying assumption that the counting proceses have no jumps in common implies that the martingales are orthogonal).

#figure(diagram(spacing: (12mm, 7.5mm), debug: false, node-stroke: 0.7pt, node-inset: 15pt, label-size: 6pt, {
    let (novisit, treat_visit, treat_visit_2, death) = ((0,0), (-1.5,1.5), (1.5,1.5), (0, 3))
    node(novisit, [$A(0)=1$ (0)])
    node(treat_visit, [1st patient visit (1) \ change treatment to $1$]) 
    node(treat_visit_2, [1st patient visit (2) \ change treatment to $0$])
    node(death, [Terminal event (3)])

    edgemsm(novisit, treat_visit, [$h^(a,1) (t)$])
    edgemsm(novisit, treat_visit_2, [$h^(a,0) (t)$])
    
    edgemsm(novisit, death, [$h_1^y (t)$])
    edgemsm(treat_visit, death, [$h_2^y (t, s, 1)$])
    edgemsm(treat_visit_2, death, [$h_2^y (t, s, 0)$])
}), caption: [A multi-state model allowing one visitation time for the treatment with the possible treatment values $cal(A)={0,1}$. ])
<fig:multi-state>

The observed times for the jumps between states are
$
    T_0 &= inf {t > 0 | X(t) != 0}, \
    Delta &= X(T_0), \
    T &= inf {t > 0 | X(t) = 3}.
$
Also note that $V = inf {t > 0 | X(t) in {1, 2}}$ represents the first visitation time for the treatment.
We will intervene on this time, so that the patient stays treated after the first visitation time.
but still visits the doctor at the same time.

We can also define the observed counting processes for the multi-state model $N=(N^(01), N^(02), N^(03), N^(13), N^(23))$ as
$
    N^(01) (t) &= bb(1) {T_0 <= t, Delta = 1}, \
    N^(02) (t) &= bb(1) {T_0 <= t, Delta = 2}, \
    N^(03) (t) &= bb(1) {T_0 <= t, Delta = 3}, \
    N^(13) (t) &= bb(1) {T <= t, Delta = 1}, \
    N^(23) (t) &= bb(1) {T <= t, Delta = 2}.
$
The corresponding filtration is given by $cal(F)_t= sigma(N^(01) (s), N^(02) (s), N^(03) (s), N^(13) (s), N^(23) (s) | s <= t)$.
Additionally the intensities are assumed to be given by,
$
    lambda^(01)(t) &= bb(1) {t <= T_0} h^(a,1) (t), \
    lambda^(02)(t) &= bb(1) {t <= T_0} h^(a,0) (t), \
    lambda^(03)(t) &= bb(1) {t <= T_0} h_1^y (t), \
    lambda^(13)(t) &= bb(1) {T_0 < t <= T, Delta = 1} h_2^y (t, T_0, 1), \
    lambda^(23)(t) &= bb(1) {T_0 < t <= T, Delta = 2} h_2^y (t, T_0, 0),
$
in order of the counting processes, that is the compensators are absolutely continuous with respect to the Lebesgue measure (important as we shall see).
Here we take $h^(a,1) : RR_+ -> RR_+, h^(a,0) : RR_+ -> RR_+, h_1^y : RR_+ -> RR_+$ and $h_2^y : RR_+ times RR_+ times {0,1} -> RR_+$ to be fixed and non-random functions.

We fit the above multi-state model into the framework of @ryalenPotentialOutcomes and consider such processes on $[0, tau]$ for $tau > 0$.
Associated with a marked point process is a counting measure. 
Let $({0,1}, cal(A))$ be the mark space for the treatment. Then let,
$
    N^a_t (A) &= N^(01) (t) cal(1) {1 in A} + N^(02) (t) cal(1) {0 in A}, A subset.eq {0, 1}, t in [0, tau], \
    N^y_t &= N^(03) (t) + N^(13) (t) + N^(23) (t), t in [0, tau].
$
We consider a multivariate marked point process $N=(N^a, N^y)$.
Such a process can be considered as a single marked point process, but to make the notation more clear we consider it as a pair of point processes.
In @ryalenPotentialOutcomes, the intervention is a mapping, that transforms from the whole marked point process realization to a new treatment process realization.
The intervention that we will look at transforms $N_t^(a)$ to a new process $scr(N)_t^(a)$, where
$
    scr(N)^(a)_t (A) = g(t, N|_[0, t]) = cal(1) {1 in A} scr(N)^(01)_t + 0 = cal(1) {1 in A} scr(N)^(01)_t, \
$
for $g :  [0, tau] times cal(N)_tau^({0,1}) -> RR_+$ where $cal(N)_tau^({0,1}, d)$ is the space of multivariate marked point processes with $d$ components.
This is the intervention that makes treatment shifts impossible.
The intervention is in their terms "optional" but not "predictable" because the intervention $g$ depends on the information available at time $t$ and not only on the information strictly prior to $t$.
Thus the compensating measure of $scr(N)_t^(a)$ is given by
$
    scr(L)_t^a (A) &= bb(1) {1 in A} integral_0^t lambda^(01)(t) d t = bb(1) {1 in A} integral_0^t bb(1) {t <= T_0} h^(a,1) (t) d t.
$
@ryalenPotentialOutcomes uses the term canonical compensator to mean that the random part of the compensator only depends on $N$ and baseline covariates,
that is we may write $lambda^(i j)(t) = dot(lambda)^(i j)(t, N)$ and $dot(lambda)^(i, j)$ is a non-random function. This can be seen, for example for $lambda^(1 3)$, as
$
    lambda^(13)(t) = bb(1) {N^(01) (t) = 1, N^(13) (t-) = 0} h_2^y (t, inf {t > 0 | N^(01) (t) = 1}, 1).
$
A multivariate potential outcome counting process $tilde(N)$ is a potential outcome process if

1. $tilde(N)^a_t$ has compensator $scr(L)_t^a (tilde(N))$.
2. $tilde(N)^y_t$ has compensator $Lambda^y (t, tilde(N))$.

The intuition behind this definition is that the canonical compensators fully determine the distribution of a marked point process.
The canonical compensator also makes the marked point processes into a sort-of structural equation system,
where we replace the "structural" equations with the compensators.

We consider $tau^(A,B) := inf {t > 0  | N_t^a (B) != scr(N)^a_t (B)}$ for $B subset.eq {0, 1}$. Then $tau^A := inf {tau^(A,B) | B subset.eq {0, 1}}$.
For $B subset.eq {0, 1}$ with $1 in B$, we always have $scr(N)^a (B) = N^a (B)$. This is trivially also the case with $B = emptyset$.
Therefore, we have
$
    tau^A = inf {t > 0 | N^(02) (t) = 1}.
$
which is the first time that treatment is changed to 0.

Let $bb(N)_t = bb(1) {tau^A <= t}$ and $Psi^a_t$ denote the compensator with respect to the filtration $cal(F)_t$.
If our outcome process is $Y_t = bb(1) {T <= t}$, then three basic conditions for identifiability are

1. Consistency: $tilde(Y)_t bb(1) {tau^A > t} = Y_t bb(1) {tau^A > t}$.
2. Exchangeability: The intensity $lambda^(12)$ for the filtration $cal(F)_t$ is the same as it is for $cal(G)_t=cal(F)_t or sigma(tilde(Y)_s, tau >= s >= 0)$.
3. Positivity: $V_t = (bb(1) {tau^A > t}) / (scr(P)_(s in (0, t]) (1- d Psi^a (s)))$ is a uniformly integrable martingale, where $scr(P)$ denotes the product integral.
   This is the same as stating that the measure $Q$ given by $d Q = V_tau d P$ is a probability measure.

Then, $bb(E)[tilde(Y)_t] = bb(E)[Y_t V_t]$ (Theorem 1 in @ryalenPotentialOutcomes).
Note that $bb(N)_t = N^(02) (t)$¸ so $Psi^a_t = integral_0^t lambda^(02)(s) d s = integral_0^t bb(1) {s <= T_0} h^(a,0) (s) d s$.
This implies that $V_t = (1-N_t^(02)) / (exp(-integral_0^t bb(1) {s <= T_0} h^(a,0) (s) d s))$.
Define $bb(N)^(a, psi)(A) = bb(1) {tau^A <= t, scr(N)^a ({tau^a} times A) = 1}$.
Then,
$
    bb(N)_t^(a,phi) (A) &:= bb(1) {tau^A <= t,  scr(N)^a ({tau^a} times A) = 1} \
        &= cal(1) {tau^A <= t} bb(1) {scr(N)^a ({tau^a} times A) = 1} \
        &= N^(02) (t) (N^(01) (tau^A) - N^(01) (tau^A-)) cal(1) {1 in A} \
        &= 0.
$
The last follows since: If $N^(02) (t) = 1$, meaning $tau^A <= t$,
then $N^(01) (tau^A) = 0$ and $N^(01) (tau^A-) = 0$ because at most one
of the processes $N^(01)$ and $N^(02)$ can jump. Its compensator $scr(L)_t^(a,phi) (dot)$ is therefore 0.

It also follows that $Delta Phi_t^a = 0$ because the compensator is absolutely continuous with respect to the Lebesgue measure.
Let $scr(L)_t^(y,a)$ be the compensator to $bb(N)_t^(y,a) := bb(1) {tau^A <= t, N^y ({tau^a}) = 1} = 0$, i.e., 0.
Using Pål's g-formula (Theorem 2 in @ryalenPotentialOutcomes), we have
$
    cal(L)_t^a &= (scr(L)_t^a - scr(L)_t^(a,phi)) / (1-Delta Phi_t^a) = scr(L)_t^a, \
    cal(L)_t^y &= (scr(L)_t^y - scr(L)_t^(y,a)) / (1-Delta Phi_t^a) = scr(L)_y^a.
$
is the $Q$-$cal(F)_t$ compensators of $N_t^a$ and $N_t^y$, respectively.
This is the usual g-formula given in @rytgaardContinuoustimeTargetedMinimum2022.
Critically, we used that the compensator is absolutely continuous with respect to the Lebesgue measure.
The is not surprising as $V_tau$ is actually just the normal inverse probability weights given in @rytgaardContinuoustimeTargetedMinimum2022.
All considerations imply that interventional probability of dying before time $t$ is given by
$
    bb(E)[tilde(Y)_t] &= integral_0^t exp(-integral_0^s h^(a,1) (u) + h_1^y (u) d u) h_1^y (s) d s \
        &+ integral_0^t exp(-integral_0^s h^(a,1) (u) + h_1^y (u) d u) h^(a,1) (s) integral_s^t exp(-integral_s^w h_2 (u, s, 1) d u) h_2 (w, s, 1) d w d s
$
Now compare this with 
$
    bb(E)[Y_t] &= integral_0^t exp(-integral_0^s h^(a,1) (u) + h^(a,0) (u) + h_1^y (u) d u) h_1^y (s) d s \
        &+ integral_0^t exp(-integral_s^w h^(a,1) (u) + h^(a,0) (u) + h_1^y (u) d u) h^(a,1) (s) integral_s^t exp(-integral_s^w h_2 (u, s, 1) d u) h_2 (w, s, 1) d w d s \
        &+ integral_0^t exp(-integral_s^w h^(a,1) (u) + h^(a,0) (u) + h_1^y (u) d u) h^(a,0) (s) integral_s^t exp(-integral_s^w h_2 (u, s, 0) d u) h_2 (w, s, 0) d w d s 
$
which is the observed probability of dying before time $t$. According to Pål's product integral formula (Lemma 1 in @ryalenPotentialOutcomes), the previous equation can be written as 
$
    bb(E)[Y_t] &= integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h_1^y (s) bb(1) {s <= oo} dot bb(1) {s <= t} d s \
        &+ integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h^(a,1) (s) bb(1) {s <= oo} dot 0 d s \
        &+ integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h^(a,0) (s) bb(1) {s <= oo} dot 0 d s \
        &+ integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h^(a,1) (s) bb(1) {s <= oo} \
        &quad quad quad  integral_0^oo exp(-integral_s^w h_2 (u, s, 1) bb(1) {s < u <= oo} d u) h_2 (w, s, 1) bb(1) {s < w <= oo} bb(1) {s <= t} d w d s \
        &+ integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h^(a,0) (s) bb(1) {s <= oo} \
        &quad quad quad integral_0^oo exp(-integral_s^w h_2 (u, s, 0) bb(1) {s < u <= oo} d u) h_2 (w, s, 0) bb(1) {s < w <= oo} bb(1) {s <= t} d w d s
$
Note: The at-risk indicator's are present in the above formulation can be seen by the following: The zero process does not have any jump points. Hence, the first jump point is at infinity in the outer integral.
Similarly, in the inner integral, the random measure $delta_(t_1, x_1)$ does not have a second jump point.

If we do the calculation corresponding to a multi-state model where one of the intermediate states is treatment discontinuation, corresponding
to the deletion of state 1, we will get the ordinary g-formula too.

Extensions could be to stochastic interventions in an observational study with a time to operation.
Then it might make sense to intervene on the distribution of the time to operation, such that it observed hazard ratio is twice as large as the observational one.
Currently this does not fit within the framework of @ryalenPotentialOutcomes.

= Multiple event points

Note that 
$
    bb(1){tau^A <= t} = sum_k bb(1){T_k <= t, D_k = a, A(T_k) = 0, A(T_(k-1)) = ... = A_(T_(1)) = 1}
$

In my notes I found that $bb(1){T_k <= t, D_k = a, A(T_k) = 0}$ is a martingale
with compensator $integral_0^t lambda_s(t, a, 1, cal(X)) bb(1){T_(k-1) < s <= T_k} d s$.

Consider for $s < t$
$
    &bb(E)[bb(1){T_k <= t, D_k = a, A(T_k) = 0, A(T_(k-1)) = ... = A(T_1) = 1} \
        &quad quad -integral_(0)^(t) lambda_u (a, 1, cal(X)) bb(1){T_(k-1) < u <= T_k) d u bb(1){A(T_(k-1)) = ... = A(T_1) = 1} | cal(F)_s] \
        &=bb(E)[bb(1){T_(k-1) <= s} (bb(1){T_k <= t, D_k = a, A(T_k) = 0, A(T_(k-1)) = ... = A(T_1) = 1} \
            &quad quad - integral_(0)^(t) lambda_u (a, 1, cal(X)) bb(1){T_(k-1) <u <= T_k} d u bb(1){A(T_(k-1)) = ... = A(T_1) = 1} | cal(F)_s] \
            &= bb(E)[bb(1){T_k <= t, D_k = a, A(T_k) = 0} \
                &quad quad - integral_(0)^(t) lambda_s (t, a, 1, cal(X)) bb(1){T_(k-1) < s <= T_k} d s| cal(F)_s] bb(1){A(T_(k-1)) = ... = A(T_1) = 1} bb(1){T_(k-1) <= s} \
            &= 0
$

Since $integral_0^t lambda_s(t, a, 1, cal(X)) bb(1){T_(k-1) < s <= T_k, A(T_(k-1)) = ... = A(T_1) = 1} d s$
is continuous and adapted, it is predictable. It is also increasing, so it is the compensator to the process $bb(1){T_k <= t, D_k = a, A(T_k) = 0, A(T_(k-1)) = ... = A(T_1) = 1}$.
Thus $Delta Psi_t^a = 0$ (identically zero).

//  (continuous and adapted (because integrand is predictable and hence progressively measurable and the measure is the Lebesgue measure, so that is non-random, so the integral is then progressively which means adapted).

Using this decomposition, we find
$
    &bb(1)(tau^A <= t) bb(1)(scr(N)^a ({tau^a}, {1})) \
        &= sum_k bb(1){T_k <= t, D_k = a, A(T_k) = 0, A(T_(k-1)) = ... = A(T_1) = 1} bb(1)(scr(N)^a ({tau^a}, {1}) = 1) \
        &= sum_k bb(1){T_k <= t, D_k = a, A(T_k) = 0, A(T_(k-1)) = ... = A(T_1) = 1} (N^a_(tau^A)({1}) - N^a_(tau^A-)({1})) bb(1)(A(T_k) = 1) \
        &= 0
$

This means that the g-formulas stay the same as with the single event case. 

#bibliography("references/ref.bib",style: "apa")
