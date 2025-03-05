#import "@preview/fletcher:0.5.1": node, edge, diagram
// #import "template.typ": conf
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
#import "@preview/cetz:0.3.1"
#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#set cite(form: "prose")
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

We consider a multi-state model with at most one visitation time for the treatment (that is at most one point where treatment may change), 
no time-varying covariates, and no baseline covariates. In the initial state everyone starts as treated (0). We consider the setting with no censoring. 
The multi-state model is shown in @fig:multi-state. 
//As always, we will assume finite-variation martingales in the below, so that our underlying assumption that the counting proceses have no jumps in common implies that the martingales are orthogonal).

#figure(diagram(spacing: (12mm, 7.5mm), debug: false, node-stroke: 0.7pt, node-inset: 15pt, label-size: 6pt, {
    let (novisit, treat_visit, treat_visit_2, death) = ((0,0), (-1.5,1.5), (1.5,1.5), (0, 3))
    node(novisit, [$A(0)=1$ (0)])
    node(treat_visit, [1st patient visit (1) \ stay on treatment ($A(T_1) = 1$)]) 
    node(treat_visit_2, [1st patient visit (2) \ drop treatment ($A(T_1) = 0$)])
    node(death, [Terminal event (3)])

    edgemsm(novisit, treat_visit, [$h^(a) (t) pi(A_1 = 1 | T_1 = t, D_1 = a)$])
    edgemsm(novisit, treat_visit_2, [$h^(a) (t) pi(A_1 = 0 | T_1 = t, D_1 = a)$])
    
    edgemsm(novisit, death, [$h_1^y (t)$])
    edgemsm(treat_visit, death, [$h_2^y (t, s, 1)$])
    edgemsm(treat_visit_2, death, [$h_2^y (t, s, 0)$])
}), caption: [A multi-state model allowing one visitation time for the treatment with the possible treatment values 0/1. ])
<fig:multi-state>

We will represent the observations from such a multi-state model as a marked point process.
This means that we can represent the observed data as $O = (T_1, D_1, A_1, T_2, D_2, A_2) in ((0, oo] times ({a, y} times {0, 1, emptyset} union {nabla}))^2 := cal(N)^X$.
The mark space is given as $X = {a, y} times {0, 1, emptyset} union {nabla}$.
Here $nabla$ denotes the empty mark, representing an event that never occurs (which may be the case for the second event) and $emptyset$ is used for the outcome,
$T_i$ denotes the time of the $i$'th event, $D_i$ is what kind of jump that occurs (so $D_1 in {a, y}$),
and $A_i$ is the treatment value at the $i$'th event (the second event is always an outcome so $A_2 = nabla$).
//We consider observations in $[0, tau]$ for $tau > 0$.
// Let $(P, Omega)$ be a probability space. 

Consider a given probability measure $P$. 
Let $cal(F)$ be the smallest $sigma$-algebra
making the mappings for the sequence
$
    cal(N)^X in.rev (t_1, d_1, a_1, t_2, d_2, a_2) arrow.bar t_1, \
    cal(N)^X in.rev (t_1, d_1, a_1, t_2, d_2, a_2) arrow.bar d_1, \
    cal(N)^X in.rev (t_1, d_1, a_1, t_2, d_2, a_2) arrow.bar a_1, \
    cal(N)^X in.rev (t_1, d_1, a_1, t_2, d_2, a_2) arrow.bar t_2, \
    cal(N)^X in.rev (t_1, d_1, a_1, t_2, d_2, a_2) arrow.bar d_2, \
    cal(N)^X in.rev (t_1, d_1, a_1, t_2, d_2, a_2) arrow.bar a_2
$
measurable (for the real numbers $RR_+ = (0, oo)$ we use the Borel $sigma$-algebra $cal(B) (0, oo)$). Next,
we consider the associated measure given by
$
    N ((0, t] times dot times dot) = sum_(j = 1)^2 bb(1) {t_j < oo} delta_((t_j, d_j, a_j)) ( (0, t] times dot times dot) = sum_(j = 1)^2 bb(1) {t_j <= t} delta_((d_j, a_j)) (dot times dot).
$
on $( RR_+ times X, cal(B)(RR_+) times cal(X)))$.
Putting in our observations to the above, we get a random measure that generates a filtration $cal(F)_t = sigma( N ((0, s] times D times A) | s <= t, D subset.eq {a, y}, A subset.eq {0, 1, emptyset})$.
Then, we are in the canonical setting if we use the filtered probability space $(Omega, cal(F), (cal(F)_t)_(t >= 0), P)$.
To follow along @ryalenPotentialOutcomes, we restrict the observations to the interval $[0, tau]$ for $tau > 0$.
This means that the observations beyond the point $tau$ have an event time set to $oo$ and the mark set to the empty mark $nabla$.
// Specifically, define a new mapping from $cal(N)^X$ which maps the element $O$ to $O|_t$
// with $O = (t_1^*, d_1^*, a_1^*, t_2^*, d_2^*, a_2^*) in cal(N)^X$ such that 
// $
//     (t_n^*, d_n^*, a_n^*) mapsto cases(
//         (t_n, d_n, a_n) & "if" t_n <= t, \
//         (oo, nabla) & "otherwise" 
//         )
// $
//Then, we really observe $O_tau$ and not $O$. T
Throughout, we assume that the observations are observed in the interval $[0, tau]$.
We make the intervention definition specific to our marked setting.
The important details will be the same.

Consider a mapping $g : RR_+ times {a,y} -> {0, 1}$, representing a treatment protocol at the visitation time, e.g. $g(t_1, d_1) = 1$ if always treat at visitation time. //cases(1 & "if" d_1 = a, A_0 & "otherwise")$ (note that $A_0 = 1$).
Then, we can consider a new point process given by
$
    O^g = (T_1, D_1, g(T_1, D_1), T_2, D_2, A_2).
$
and $N^g = bb(1) {T_1 < oo} delta_((T_1, D_1, g(T_1, D_1))) + bb(1) {T_2 < oo} delta_((T_2, D_2, A_2))$
as the corresponding random measure. Let $T^a$ be the possible time to deviation from the protocol $g$.
That is,
$
    T^a = cases(
        T_1 & "if" D_1 = a "and" g(T_1, D_1) != A_1, \
        oo & "otherwise"
        )
$
Next, we define the potential outcome process $tilde(O)$.
For this, we need to define the canonical compensator.
For $N$, the counting process measure, the compensating measure $Lambda = Lambda (O, d t, d m, d a)$ can be chosen
to be a kernel from $cal(N)_tau^X$ to $RR_+ times X$.
This means that $Lambda(o, d t, d m, d a)$ is a measure on $RR_+ times {a, y} times {0, 1, emptyset}$ such that for each $o in cal(N)_tau^X$,
$Lambda(o, dot times dot times dot)$ is a measure on $RR_+ times {a, y} times {0, 1, emptyset}$ and $o mapsto Lambda(o, S)$ is measurable
for each $S in cal(B)(RR_+) times {a, y} times {0, 1, emptyset}$.
In our presentation we will make explicit use of this compensator.
The intuition behind this definition is that the canonical compensators uniquely determine the distribution of a marked point process,
that is the distribution of the jump times and marks.
The canonical compensator also makes the marked point processes into a sort-of structural equation system,
where we replace the "structural" equations with the compensators.
First, we look at the case
$
    Lambda (O, d t, d m, d a) &= delta_a (d m) h_a (t) bb(1) {t <= T_1}  (delta_1 (d a) pi(A_1 = 1 | T_1 = t, D_1 = a) \
        &#h(1cm) + delta_0 (d a) (1-pi(A_1 = 1 | T_1 = t, D_1 = a))) d t \
        &+ delta_y (d m) h_1^y (t) bb(1) {t <= T_1} d t \
        &+ delta_y (d m) h_2^y (t, s, 1) bb(1) {D_1 = a, A_1 = 1, T_1 < t <= T_2} d t \
        &+ delta_y (d m) h_2^y (t, s, 0) bb(1) {D_1 = a, A_1 = 0, T_1 < t <= T_2} d t 
$
Here we take $h^(a,1) : RR_+ -> RR_+, h^(a,0) : RR_+ -> RR_+, h_1^y : RR_+ -> RR_+$ and $h_2^y : RR_+ times RR_+ times {0,1} -> RR_+$ to be fixed and non-random functions,
$pi: {0, 1} times RR_+ times {a, y} -> [0, 1]$ to be a fixed and non-random function, such that $pi(A_1 = 1 | T_1 = t, D_1 = a) + pi(A_1 = 0 | T_1 = t, D_1 = a) = 1$.
Afterwards, we look at the case that the total compensator is not absolutely continuous.
This turns out to be important. Notice the sums between different types of events.
This corresponds to assuming that the events cannot happen at the same time. 
Let us consider the static intervention $g(t, d) = 1$ and find the canonical compensator for
$O^g$. This can be found by computing $N^g$ at various points.
For example,
$
    N^g ((0, t] times {a} times {0}) &= 0 \
    N^g ((0, t] times {a} times {0, 1}) &= N ((0, t] times {a} times {0, 1}) \
    N^g ((0, t] times {y} times {emptyset}) &= N ((0, t] times {y} times {emptyset}) 
$
// use the second compensator first to find the first one. 
from which the canonical compensator is easily derived to be,
$
    Lambda^(g) (O^g, d t, d m, d a) &= delta_a (d m) h_a (t) bb(1) {t <= T_1} delta_1 (d a) d t \
        &+ delta_y (d m) h_1^y (t) bb(1) {t <= T_1} d t \
        &+ delta_y (d m) h_2^y (t, s, 1) bb(1) {D_1 = a, A_1 = 1, T_1 < t <= T_2} d t \
        &+ delta_y (d m) h_2^y (t, s, 0) bb(1) {D_1 = a, A_1 = 0, T_1 < t <= T_2} d t 
$
A process is a potential outcome $tilde(O)$ if its compensator is given by $Lambda^(g) (tilde(O), d t, d m, d a)$.
The outcome of interest is defined as a function of the data $O$, that is $Y = Y(O)$.
The associated counterfactual filtration is $tilde(cal(F))_t = sigma(tilde(N) ((0, s] times D times A) | s <= t, D subset.eq {a, y}, A subset.eq {0, 1, emptyset})$.
Conceptually, we should think of consistency in this setting as $O = tilde(O)$ if $T^A = oo$ and $O = (tilde(T)_1, tilde(D)_1, A_1, T_2, D_2, A_2)$
if $T^A < oo$.
In this sense, $tilde(Y) = Y(tilde(O))$ is the potential outcome process of interest.
In our setting, we put $Y_t (O) = bb(1) {T_1 <= t, D_1 = y} + bb(1) {T_2 <= t, D_2 = y}$,
corresponding to a terminal event before time $t$.
    
//An intervention is then simply a sequence of mapping $g_k : H_(k-1) times (T_k, D_k) -> {0, 1}$.
// IN the case where the event is infity we do nothing

Consider the intervention $g(t, d) = 1$.
First, note that $(T^a <= t) = (D_1 = a, A_1 = 0, T_1 <= t) in cal(F)_t$ for each $t > 0$ which 
means that $T^a$ is a stopping time with respect to the filtration $cal(F)_t$.
Then three basic conditions for identifiability are

1. Consistency: $tilde(Y)_t bb(1) {T^A > t} = Y_t bb(1) {T^A > t}$ for all $t > 0$ $P$-a.s.
2. Exchangeability: The compensator $Lambda (d t, {a}, d a)$ for the filtration $cal(F)_t$ is the same as it is for $cal(G)_t=cal(F)_t or sigma(tilde(Y)_s, tau >= s >= 0)$.
3. Positivity: $W_t = (bb(1) {T^A > t}) / exp(-Lambda ((0, t] times {a} times {0})) = (1-bb(1){T_1 <= t, D = a, A = 0}) / exp(-integral_0^t bb(1) {s <= T_1} h^(a) (s) pi(A_1 = 0 | T_1 = s, D_1 = a) d s)$
 a uniformly integrable martingale, where $scr(P)$ denotes the product integral.
   This is the same as stating that the measure $Q$ given by $d Q = V_tau d P$ is a probability measure.

Then, $bb(E)[tilde(Y)_t] = bb(E)[W_t Y_t]$ (Theorem 1 in @ryalenPotentialOutcomes).
This construction is different from the usual approach
in the sense that inverse probability weighting is used to derive the g-formula and not the other way around.
Note that $W_t$ cannot be directly interpreted as a likelihood ratio of interest, for in this case
the likelihood ratio that @rytgaardContinuoustimeTargetedMinimum2022 dictates is
$
    macron(W)_t = ((bb(1) {A(T_k) = 1}) / (pi_(T_k) (A(T_k) = 1 | D(T_k) = a, cal(F)_(T_K))))^(bb(1) {T_k <= t, D_k = a})
$
The difference is that $macron(W)_t$ corresponds to the likelihood ratio in which the difference between the two probability measures is that we replace the intensity from state 0 to 2 with 0 and the intensity from state 0 to 1 with $h^a (t)$.  
On the other hand, $W_t$ corresponds to likelihood ratio in which the difference between the two probability measures is that we replace the intensity from state 0 to 2 with 0.
However, this is not a formal proof that the g-formula in @rytgaardContinuoustimeTargetedMinimum2022
is not the same as the one in @ryalenPotentialOutcomes. There may be multiple inverse probability weightings that are valid.
//In their notation $V_t = W_t$, $bb(N)_t = bb(1) {T^a <= t}$ and $Psi^a_t = Lambda ((0, t] times {a} times dot)$.

We are now ready to compare the two approaches.
The approach in @rytgaardContinuoustimeTargetedMinimum2022 stipulates that the $Q$-$cal(F)_t$ compensator of $N ((0, t] times {a} times dot)$ is given by
$Lambda^Q ((0, t], {a}, dot) = Lambda^(g) ((0, t], {a}, dot)$ and that the $Q$-$cal(F)_t$ compensator of $N ((0, t] times {y} times dot)$ is given by $Lambda^Q ((0, t], {y}, dot) = Lambda ((0, t], {y}, dot)$.
We will show that this is indeed the case if $Lambda ({t} times {a} times {0}) = 0$ which happens if $N ((0, t] times {a} times {0})$ has a compensator which is absolutely continuous with respect to the Lebesgue measure.
To this end, we shall calculate $N^(g times a) (t) = [N^g ((0, dot] times {a} times A), bb(1) {T^a <= dot]_t = sum_(s <= t) bb(1) {1 in A} N^g ({s} times {a} times A)) bb(1) {T^a = s} = 0$ - the optional covariation of the two processes.
This is zero because the two processes have no jumps in common, which is due to the fact that you cannot have a visitation time in which the doctor both treats and does not treat, i.e.
you cannot jump to state 1 and 2 at the same time.
Since we have that $N ((0, t] times {y} times dot)$ and $N^g ((0,t] times {a} times dot)$ cannot jump at the same time (follows from the decomposition), then the same argument applies to $N^(g times y) (t) = [N ((0,dot] times {y} times dot), bb(1) {T^a <= dot}]_t$
Thus their respective compensators are $Lambda^(g times a) ((0,t] times dot) = Lambda^(g times y) ((0,t] times dot) = 0$.
Using Pål's g-formula (Theorem 2 in @ryalenPotentialOutcomes) gives
$
    Lambda^Q ((0, t] times {a}, A) &= integral_((0, t]) (d Lambda^g (dot times {a} times A) - d Lambda^(g times  a) (dot times A)) / (1 - Delta Lambda_s^a ({0}))  = integral_((0, t]) (Lambda^g (dot times {a} times A) - 0) / (1 - 0) \
        &= Lambda^g ((0, t] times {a} times A) \ \ 
        Lambda^Q ((0, t] times {y}, {emptyset}) &= integral_((0, t]) (d Lambda^g (dot times {y} times {emptyset}) - Lambda^(g times y) (dot times {emptyset})) / (1 - Delta Lambda_s^a ({0}))  = integral_((0, t]) (Lambda (dot times {y}, {emptyset}) - 0) / (1 - 0) \
        &= Lambda ((0,t] times {y} times {emptyset}).
$
Critically, we used that the compensator is absolutely continuous with respect to the Lebesgue measure.
//The counterexample that is considered in @ryalenPotentialOutcomes is when the compensator is a bit artificial,
//because it does not take into account that death is a terminal event.
//In this sense, the patient is allowed to have visitation times after they die. 

Now we assume in contrast that the total compensator is 
$
    Lambda ((0, t] times {a} times {0, 1}) = integral_((0, t]) bb(1) {s <= T_1} d K(s) = c bb(1) {1 <= T_1 and t}, c in (0, 1)
$
where
$
    K (s) = c bb(1) {1 <= s}
$
Evidently, $Lambda ((0, t] times {a} times d a) = sum_(m=0,1) delta_(m)(d a) pi(A(T_1) = m | D(T_1) = a, T_1 = s) Lambda ((0, t] times {a} times {0, 1})$
is predictable, increasing, cadlag, but not absolutely continuous with respect to the Lebesgue measure.
We find that with the same calculations as previously, 
$
    Lambda^Q ({s} times {a} times {1}) &= 1/(1 - Lambda ({s} times {a} times {0})) (Lambda^g ({s} times {a} times {1}) - Lambda^(g times  a) ({s} times {a} times {1})) \
        &= 1/(1 - pi(A(T_1) = 0 | D(T_1) = a, T_1 = s) c bb(1) {s <= T_1, s = 1)) Lambda^g ({s} times {a} times {1})
$
If $s!=1$, then $Lambda^Q ({s} times {a} times {1})  = Lambda^g ({s} times {a} times {1})$.
However, with positive probability, $Lambda^Q ({s} times {a} times {1})  = 1/(1 - pi(A(T_1) = 0 | D(T_1) = a, T_1 = 1) c bb(1) {1 <= T_1)) Lambda^g ({s} times {a} times {1}) != Lambda^g ({s} times {a} times {1})$ for $s=1$.
A similar conclusion be drawn for the other compensators. 

// predictable because X = X delta K + K_-
//Proposition 1 in @ryalenPotentialOutcomes states that $W_t = cal(E) (- (N_t (s, a, 0) - Lambda_t (s, a, 0)))$, where $cal(E)$ is the stochastic exponential.
//Using Theorem 15.2.6 of @cohen2015stochastic can then give the result, by finding the compensators under $Q$ like we did with $Lambda^(g)$.

// In this case, the proof is relatively easy.
// Note that the marked point process in this case can be identified with
// the new multivariate counting processes $bold(N)=(N_t^(a,0), N_t^(a,1), N_t^y) = (N ((0, t] times {a} times {0}), N ((0, t] times {a} times {1}), N ((0, t] times {y} times {emptyset}))$.
// Note that
// $
//     W_t &= (1- bb(1) {T_1 <= t, D_1 = a, A_1 = 0})/ exp(-Lambda ((0, t] times {a} times {0})) = (1-N_t^(a,0)) / exp(-integral_0^t bb(1) {s <= T_1} h^(a) (s) pi(A_1 = 0 | T_1 = s, D_1 = a) d s) \
//         &= (0 / (bb(1) {s <= T_1} h^(a) (s) pi(A_1 = 0 | T_1 = s, D_1 = a)))^(bb(1) {N_t^(a,0) = 1}) exp(-Lambda_*^(y) (t) - Lambda_*^(a,01) (t)) / exp(-Lambda^(y) (t) - Lambda^(a,0) (t) - Lambda^(a,01) (t))
// $

// Note that $bb(N)_t = N^(02) (t)$¸ so $Psi^a_t = integral_0^t lambda^(02)(s) d s = integral_0^t bb(1) {s <= T_0} h^(a,0) (s) d s$.
// This implies that $V_t = (1-N_t^(02)) / (exp(-integral_0^t bb(1) {s <= T_0} h^(a,0) (s) d s))$.
// Note that that is the ordinary likelihood ratio between two measures $P$ and $tilde(P)$, where the intensities for transition from 0 to 2 is different, $tilde(lambda)^(02) = 0$, but the others are otherwise the same $tilde(lambda)^(i j) = lambda^(i j)$ for $i j != 02$.
// Indeed,
// $
//     V_t = ((0)/({t <= T_0} h^(a,0) (t)))^(bb(1) {Delta = 2, T_0 <= t}) exp(-tilde(Lambda)_dot (t))/ exp(-Lambda_dot (t)) =  (d tilde(P))/ (d P) #scale(y: 200%)[|]_(cal(F)_t).
// $    
// so $V_t$ is a likelihood ratio (note that $bb(1) {Delta = 2, T_0 <= t} = 1$ if and only if there has been a jump in $N^(02)$ before $t$).
// The result in @ryalenPotentialOutcomes can now be derived directly by utilizing that solves a stochastic integral equation (Volterra integral equation); see (2.7.8) of @andersenStatisticalModelsBased1993
// $
//     V_t &= 1 + sum_(h in {01, 02, 03, 13, 23}) integral_0^t V_(s-) ( (d tilde(Lambda)_h (s)) / (d Lambda_h (s)) - 1 - (Delta tilde(Lambda)_dot (s) - Delta Lambda_dot (s)) / (1 - Delta Lambda_dot (s))) ( d N_h (s) - d Lambda_h (s)) \
//         &= 1 - integral_0^t V_(s-) ( d N^(02) (s) - d Lambda^(02) (s)).
// $
// By consistency and the above result
// $
//     bb(E)[Y_t V_t] &= bb(E)[tilde(Y)_t V_t] = bb(E) [tilde(Y)_t] - bb(E) [integral_0^t tilde(Y)_t V_(s-) (d N^(02) (s) - d Lambda^(02) (s))] \
//         &= bb(E) [tilde(Y)_t]
// $
// if we can show that $bb(E)[integral_0^t tilde(Y)_t V_(s-) (d N^(02) (s) - d Lambda^(02) (s))] = 0$. Note that $V_(s-)$ is predictable as it is adapted and left-continuous (both filtrations).
// Moreover, $tilde(Y)_t$ is predictable with respect to the filtration $cal(G)_t$. By exchangeability, $N^(02) (s) - Lambda^(02) (s)$ is a martingale with respect to $cal(G)_t$, too.
// An integrated predictable process with respect to a martingale is a martingale, so the resulting expectation is zero.

== Notes to self (do not read!)

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
which is the observed probability of dying before time $t$.

Note to self: According to Pål's product integral formula (Lemma 1 in @ryalenPotentialOutcomes), the previous equation can be written as 
$
    bb(E)[Y_t] &= integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h_1^y (s) bb(1) {s <= oo} dot bb(1) {s <= t} d s \
        &+ integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h^(a,1) (s) bb(1) {s <= oo} dot 0 d s \
        &+ integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h^(a,0) (s) bb(1) {s <= oo} dot 0 d s \
        &+ integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h^(a,1) (s) bb(1) {s <= oo} \
        &quad quad quad  integral_0^oo exp(-integral_s^w h_2 (u, s, 1) bb(1) {s < u <= oo} d u) h_2 (w, s, 1) bb(1) {s < w <= oo} bb(1) {s <= t} d w d s \
        &+ integral_0^oo exp(-integral_0^s h^(a,1) (u) bb(1) {u <= oo} + h^(a,0) (u) bb(1) {u <= oo} + h_1^y (u) bb(1) {u <= oo} d u) h^(a,0) (s) bb(1) {s <= oo} \
        &quad quad quad integral_0^oo exp(-integral_s^w h_2 (u, s, 0) bb(1) {s < u <= oo} d u) h_2 (w, s, 0) bb(1) {s < w <= oo} bb(1) {s <= t} d w d s
$
The at-risk indicator's are present in the above formulation can be seen by the following: The zero process does not have any jump points. Hence, the first jump point is at infinity in the outer integral.
Similarly, in the inner integral, the random measure $delta_((t_1, x_1))$ does not have a second jump point.

If we do the calculation corresponding to a multi-state model where one of the intermediate states is treatment discontinuation, correspondin
to the deletion of state 1, we will get the ordinary g-formula too.

The g-formula can fail in other situations, even if $Delta Psi_t^a = 0$.
In this case, it has to be possible for $scr(N)_t^(a)$ to jump at other times than the jump times of $N_t^(a)$.
Consider the example multi-state model in @fig:multi-state2.

#figure(diagram(spacing: (12mm, 7.5mm), debug: false, node-stroke: 0.7pt, node-inset: 15pt, label-size: 6pt, {
    let (novisit, treat, covariate, death) = ((0,0), (-1.5,1.5), (1.5,1.5), (0, 3))
    node(novisit, [$A(0)=1$ (0)])
    node(treat, [treatment (2)])
    node(covariate, [covariate (1)])
    node(death, [Terminal event (3)])

    edgemsm(novisit, covariate, [$h^(ell) (t)$])
    edgemsm(novisit, treat, [$h^(a) (t)$])
    
    edgemsm(novisit, death, [$h_0^y (t)$])
    edgemsm(treat, death, [$h_2^y (t, s, 1)$])
    edgemsm(covariate, death, [$h_1^y (t, s)$])
}), caption: [A multi-state model allowing a visitation time for the treatment and a different visitation time for the covariate ($P$). ])<fig:multi-state2>

We use instead the intervention of treatment given by $bold(n)_t^a (phi) = phi^(01)$, that is treat if a covariate/comorbidity changed. 
In this case $bb(1) {tau^A <= t} = N^(01) (t) + N^(02) (t)$. However,
$
    bb(N)^(a, psi) = bb(1) {tau^A <= t, scr(N)^a_tau - scr(N)^a_(tau-) = 1} = N_t^(01).
$
So that the compensator is $cal(L)_t^a = 0 != integral_0^t lambda^(01)(s) d s$. If we calculate the $Q$-compensator for all the other states we get a multi-state model as illustrated in @fig:multi-state3.

#figure(diagram(spacing: (12mm, 7.5mm), debug: false, node-stroke: 0.7pt, node-inset: 15pt, label-size: 6pt, {
    let (novisit, treat, covariate, death) = ((0,0), (-1.5,1.5), (1.5,1.5), (0, 3))
    node(novisit, [$A(0)=1$ (0)])
    node(treat, [treatment (2)])
    node(covariate, [covariate (1)])
    node(death, [Terminal event (3)])
    
    edgemsm(novisit, death, [$h_0^y (t)$])
    edgemsm(treat, death, [$h_2^y (t, s, 1)$])
    edgemsm(covariate, death, [$h_1^y (t, s)$])
}), caption: [A multi-state model allowing a visitation time for the treatment and a different visitation time for the covariate ($Q$). ]) <fig:multi-state3>
//Extensions could be to stochastic interventions in an observational study with a time to operation.
//Then it might make sense to intervene on the distribution of the time to operation, such that it observed hazard ratio is twice as large as the observational one.
//Currently this does not fit within the framework of @ryalenPotentialOutcomes.

= Multiple event points

Note that 
$
    bb(1){tau^A <= t} = sum_k bb(1){T_k <= t, D_k = a, A(T_k) = 0, A(T_(k-1)) = ... = A_(T_(1)) = 1}
$

In my notes I found that $bb(1){T_k <= t, D_k = a, A(T_k) = 0}$ is a martingale
with compensator $integral_0^t lambda_s (t, a, 1, cal(X)) bb(1){T_(k-1) < s <= T_k} d s$.

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

In the situation with dynamic treatment based on the history, i.e.,  $pi^*(l, phi, t, d x) = delta_{g(l, phi, t)}(d x)$, we will likely get the same result.
Importantly, we need that the time-varying covariates cannot jump at the same time as the treatment visitation times and moreover that $Delta Psi_t^a = 0$, which is the case if $Psi_t^a$ is absolutely continuous with respect to the Lebesgue measure.

#bibliography("references/ref.bib",style: "apa")
