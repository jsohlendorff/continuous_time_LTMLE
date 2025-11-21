// Typst packages
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.1": arkheion
#import "@preview/ctheorems:1.1.3":
#import "@preview/cheq:0.3.0": checklist
#import "@preview/numty:0.0.5" as nt
#show: checklist

= Checklist

- [x] Introduction
- [x] Construction of counterfactuals
- [x] Equivalence with sequential criteria
- [x] Full vs partial sequential exchangeability. 
- [x] Comparison of the identifying functionals (@ryalenPotentialOutcomes and @rytgaardContinuoustimeTargetedMinimum2022).
- [~] Uniqueness of identifying formula (Works with more than two treatment levels?)
- [~] Right-censoring (Need EIF under right-censoring + construction of counterfactuals?)
- [~] Comparison with CAR

// Math setup
// Definition, theorems, proofs, etc...
#show math.equation: set text(9pt)
#show: thmrules.with(qed-symbol: $square$)

// Numbering
#set math.equation(numbering: "(1)")
// Label equation if referenced; otherwise do no label equations
#show math.equation: it => {
  if it.block and not it.has("label") [
    #counter(math.equation).update(v => v - 1)
    #math.equation(it.body, block: true, numbering: none)#label("empty")
  ] else {
    it
  }  
}
#set heading(numbering: "1.a)")
#set footnote(numbering: "*")

// References and citations
#set cite(form: "prose")
#show ref: it => {text(fill: maroon)[#it]}

// Formatting
#set text(size: 10pt)
#set image(width: 75%)

// Set up Arkheion template (arXiv-like Typst template)
#show: arkheion.with(
    title: "Identification and Estimation of Causal Effects under Treatment-Assigned-At-Visit Interventions in Continuous Time",
    authors: (
        (name: "Johan S. Ohlendorff", email: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen", orcid: "0009-0006-8794-6641"),
        (name: "Pål Ryalen", email: "pal.ryalen@medisin.uio.no", affiliation: "University of Oslo", orcid: "0000-0002-3236-6782"),
        (name: "Kjetil Røysland", email: "kjetil.roysland@medisin.uio.no", affiliation: "University of Oslo", orcid: "0000-0001-5808-4903"),
        (name: "Anders Munch", email: "a.munch@sund.ku.dk", affiliation: "University of Copenhagen", orcid: "0000-0003-4625-1465"),
        (name: "Thomas A. Gerds", email: "tag@biostat.ku.dk", affiliation: "University of Copenhagen", orcid: "0000-0002-5955-816X"),
    ),
    abstract: [
        Marginal structural models (MSMs) offers an approach to estimating longitudinal causal
        effects in discrete time. However, their reliance on fixed-grid data limits their applicability
        to irregularly spaced observations. @rytgaardContinuoustimeTargetedMinimum2022 investigated a continuous-time jump process
        setting where treatment intervention was applied to assigned treatment, but not the timing of visits.
        This article provides a formal proof of the causal interpretation of the estimands,
        constructs counterfactual distributions, discusses the uniqueness of the identifying formula,
        and compares the findings with recent work by @ryalenPotentialOutcomes.
    ],
    keywords: ("causal inference", "continuous-time", "coarsening at random", "treatment-assigned interventions"),
)

// In discrete time, the two formula are the same because every discrete time is a visitation event?
// What if we are still in discrete time, but the treatment decision is not made at every time point, but randomly; then it maybe does not relate to discrete time theories

= Introduction

Robins’ theory of causal inference for complex longitudinal data structures offers a robust 
framework for identifying causal effects when treatments and covariates are measured at discrete 
time points (@robins1986).  This approach seeks to estimate the counterfactual 
mean outcome under a specific treatment intervention. This pursuit led to the development of the 
g-formula, a method that identifies the counterfactual mean under specific conditions, 
via the observed data distribution (@robins1986, @robins2000marginal, @RobinsLongitudinal2001).  Crucially, the g-formula relies on several key assumptions, including consistency, 
sequential exchangeability, and positivity.

// The exchangeability assumption is often dubbed "No unmeasured confounding";
// however that term is somewhat misleading, as
// there are actually multiple version of sequential exchangeability (@whatif).

However, many real-world scenarios involve continuous-time processes where treatments and 
covariates can change at subject-specific times, representing a significant challenge for 
traditional discrete-time approaches. To address this, @lok2008 extended Robins’ framework to 
continuous time using nested structural models, enabling causal inference in continuous-time 
settings through the estimation of a counterfactual outcome process, particularly within 
survival analysis contexts. Despite these advancements, these models still place strong 
structural assumptions.

Subsequently, it was discussed in @gill2023causalinferencecomplexlongitudinal how to obtain a general continuous-time g-formula 
within counting process settings, extending the discrete-time g-formula of @gill2023causalinferencecomplexlongitudinal
to accommodate marginal structural models in continuous time.  @rytgaardContinuoustimeTargetedMinimum2022 explored a 
specific intervention where treatment timing remains constant but treatment decisions are made 
at each visit, providing a continuous-time g-formula without a rigorous proof and accompanying 
estimation techniques.  More recently, @ryalenPotentialOutcomes developed a potential outcomes framework 
for causal inference in continuous time, establishing conditions for the identifiability of the 
counterfactual mean outcome under continuous-time treatment interventions.  Despite similarities 
in their approaches, the identification formulae may not generally be the same.
In many practical cases, the identification formulae do however coincide.
Here, uniqueness of the identifying functional is also discussed. 

We establish formal conditions under which the g-formula in @rytgaardContinuoustimeTargetedMinimum2022 identifies the counterfactual mean outcome under a continuous-time treatment intervention.
While that work introduced a g-formula and a sequential exchangeability condition, it did not provide a proof of identifiability.
Here, we present such a proof under slightly modified but intuitively related conditions and derive an equivalent martingale formulation.
Our approach fits naturally within the potential outcomes framework of @ryalenPotentialOutcomes.

Notably, our exchangeability condition admits a natural extension to a full exchangeability assumption,
which is equivalent to coarsening at random (CAR) -- an extension not available in @ryalenPotentialOutcomes.
We also provide an example illustrating that full exchangeability is strictly stronger than standard exchangeability.
(Finally, we extend Theorem 25.40 of @vaart1998 to show that CAR and only CAR implies a saturated model for the observed data distribution,
as the original theorem’s conditions are not directly applicable in the continuous-time setting.)

== A (hypothetical) motivating application

Consider a longitudinal study as an example. A subject’s baseline measurements $L(0)$ and 
initial treatment assignment $A(0)$ are recorded. The subject is then followed over the 
interval $[0, T]$ with visits to the clinic/hospital. At each visitation event, the
patient either gets their blood measurements taken ($ell$ event), or the
doctor may decide on treatment based on the patients history so far ($a$ event). 
We define $N^a (t)$ and $N^ell (t)$ as the number of treatment and covariate visits, respectively, up to time $t$
and let $A(t)$ and $L(t)$ denote the measurements and treatment decision at time $t$.
The outcome, $Y_t$ is typically a function of the patient’s 
history up to time $t$, $Y_t=sigma(L(dot and t), N^ell (dot and t))$
or it may consist of a separate component such as a primary event, say $Y_t = N^y$.

To illustrate this further, consider a randomized trial.  A common scenario is that patients 
receive treatment at each doctor’s visit. However, in real-world practice, patients may 
experience adverse effects, leading the doctor to discontinue treatment. We’re interested in 
understanding what would have happened *had* the patient continued to receive treatment. We 
represent this counterfactual outcome as $tilde(Y)_t$.  Therefore, we wish to 
estimate $bb(E) [tilde(Y)_t]$.  However, this counterfactual outcome is not 
observed directly for all subjects, presenting a key challenge.

= Notation and setup

Let $(Omega, cal(F), P)$ be a measure space.
We assume that all measurements are assumed to take place 
over a time interval $[0, T]$
where $t=0$ denotes baseline and $T>0$ denotes the time to end-of-study.
First, we formulate the setting of 
@rytgaardContinuoustimeTargetedMinimum2022.
We observe trajectories of the process
$zeta(t) = (N^a (t), A (t), N^ell (t), L (t), N^y (t), N^d (t))$,
where $zeta(t)$ is a multivariate jump process on $[0, T]$.

We have $Delta L(t) != 0$ only if $Delta N^ell (t) != 0$
and $Delta A(t) != 0$ only if $Delta N^a (t) != 0$.
To simplify things a bit, we suppose that
$
    P(inter_(t in [0, T]) (A(t) in cal(A))) = P(inter_(t in [0, T]) (L(t) in cal(L))) = 1
$
and 
$
    cal(A) &= {a_1, dots, a_(d_a)} subset.eq RR, \
    cal(L) &= {l_1, dots, l_(d_l)} subset.eq RR^k.
$
This means that all considered processes are jump processes. 
It is implicitly assumed that $(N^d, N^y, N^a, N^ell)$
forms a multivariate counting process (@andersenStatisticalModelsBased1993).
Importantly, we also make the assumption of no explosion of $N$
which is that $P(sum_(x=a,ell,d, y) N^x (T) < oo) = 1$.
// In the first sections, we will be interested in identification and
// thus not explicitly state anything about the statistical model $cal(M) = {P_theta : theta in Theta}$,
// but only work with the true data-generating measure $P$.
Now we can let, for $n >= 1$
$
    T_((n)) = inf {t > T_((n-1)) : N^y (t) + N^a (t) + N^ell (t) > n} "with" T_((0)) := 0.
$
(as is convention with point processes, we let $T_((n)) = oo$ if
$T_((n)) > T$).
These values are possibly infinite; then we can let
$
    Z_((n)) := (N^y (T_((n))), N^a (T_((n))), N^ell (T_((n))), A(T_((n))), L(T_((n)))).
$
Then, the marked point process given by $Phi = (T_((n)), Z_((n)))_(n >= 1)$ generates
the same natural filtration as the process $zeta (t)$ (Theorem 2.5.10 of @last1995marked),
that is $cal(F)_t = sigma((L(0), A(0)), Phi_t) = sigma(zeta(s), s <= t)$
#footnote[As make the assumption of no explosions, the _minimal_ jump process and the jump process are not different
    ensuring a unique measurable correspondence between the jump process and marked point process since the visitation counting process are included in $zeta$ (Theorem 2.5.10-2.5.11 of @last1995marked)].
Let further $status(k)$ be given by $status(k) = x$ if $Delta N^x (event(k)) = 1$ (with the empty mark if $event(k) = oo$. Let
$macron(Phi) = (T_((n)), macron(Z)_((n)))_(n >= 1)$ be a marked point process given by
    $
        macron(Z)_n = (status(n), treat(n), covariate(n)).
    $
    Then, since there is a measurable bijection $macron(Phi)$ and $Phi$,
we have that $cal(F)_t = sigma((L(0), A(0)), macron(Phi)_t)$,
and we can work with $macron(Phi)$ instead of $Phi$.
Intuitively, this means that the information obtained from the multivariate
jump process is the same as that obtained from the marked point process at time $t$.
Importantly, we shall work within a so-called canonical setting
which allows us to write down explicit formulae for the compensators
in terms of the mark and event time distributions (@last1995marked).
We can let $N^(a,a_j)$ be given by
$
    N^(a, a_j) (t) := sum_k bb(1) {T_((k)) <= t, status(k) = a, A(T_((k))) = a_j}
$
Let $Lambda^(a, a_j) (t)$ denote the $P$-$cal(F)_t$-compensator of $N^(a, a_j)$
and $Lambda^a (t) = sum_(j=1)^k Lambda^(a, a_j) (t)$ denote the total $P$-$cal(F)_t$-compensator of $N^a$.
By @thm:canonicalversion, we can find kernels $pi_t (dif x)$
such that
$
    Lambda^(a, a_j) (dif t) = pi_t ({a_j}) Lambda^a (dif t).
$ <eq:pi>

#lemma[
    Let $cal(F)_t$ denote the natural filtration of $macron(Phi)$.
    Then, the (predictable) stochastic kernel $pi$ from $cal(A) times cal(L) times N_({a,y,ell,d} times cal(A) times cal(L)) times RR^+$ to $cal(A)$
    $
        pi (a(0), l(0), macron(phi), t, {a_j}) = sum_k bb(1) {rho_(k-1) (macron(phi)) < t <= rho_(k) (macron(phi))) P(treat(k) = a_j | event(k) = t, status(k) = a, history(k-1) = macron(phi)^(k-1)) 
    $ <eq:piversion>
    satisfies @eq:pi where $macron(phi)^(k)$ simply consists of the random variables $(covariate(0), treat(0), dots, covariate(k), treat(k), status(k), event(k))$.
    Any kernel $pi$ from $cal(A) times cal(L) times N_({a,y,ell,d} times cal(A) times cal(L)) times RR^+$ to $cal(A)$ fulfilling @eq:pi identically satisfies
    $
        pi (treat(0), covariate(0), macron(Phi), event(k), {a_j}) = P(treat(k) = a_j | event(k), status(k) = a, history(k-1))
    $
    $P$-a.s. whenever $event(k) < oo$.
    
] <thm:canonicalversion>
#proof[
    Note that
    $
        mu_k (dif (t, delta, a, l)) &:= (P((event(k), macron(Z)_((k))) in dif (t, delta, a, l) | history(k-1)))/(P(event(k) >= t | history(k-1))) \
            &=P((treat(k), covariate(k)) in dif (a, l) | event(k) = t, status(k) = delta, history(k-1)) (P((event(k), status(k)) in dif (t, delta)  | history(k-1)))/(P(event(k) >= t | history(k-1))) \
            &={P(treat(k) in dif a | event(k) = t, status(k) = a, history(k-1)) delta_(covariate(k-1)) (dif l) bb(1) {delta = a} \
            &quad + P(covariate(k) in dif l | event(k) = t, status(k) = ell, history(k-1)) delta_(treat(k-1)) (dif a) bb(1) {delta = ell} \
            &quad + delta_(treat(k-1),covariate(k-1)) (dif (a, l)) bb(1) {delta = y}} (P((event(k), status(k)) in dif (t, delta)  | history(k-1)))/(P(event(k) >= t | history(k-1)))
    $
    According to Theorem 4.1.11 (ii) of @last1995marked, we have
    $
        Lambda (dif (t, delta, a, l)) = sum_(k=1)^oo bb(1) {event(k-1) < t <= event(k)) mu_k (dif (t, delta, a, l))
    $
    is the $P$-$cal(F)_t$ compensator associated with the point process $macron(Phi)$.
    From this, we obtain versions of the compensators on the right-hand side and the left hand side of @eq:pi
    integrating over sets of the form $(0,t] times {a} times {a_j} times cal(L)$ and
    $(0,t] times {a} times cal(A) times cal(L)$. Thus we obtain the first desired statement. 

    *NOTE:* Fix notation.
    Now use this with Theorem 4.3.2 of @last1995marked. Then, we have (almost surely)
    $
        &P(status(k) in dif delta| event(k), history(k-1)) {P(treat(k) in dif a | event(k), status(k) = a, history(k-1)) delta_(covariate(k-1)) (dif l) bb(1) {delta = a} \
            &+ P(covariate(k) in dif l | event(k), status(k) = ell, history(k-1)) delta_(treat(k-1)) (dif a) bb(1) {delta = ell} + delta_(treat(k-1),covariate(k-1)) (dif (a, l)) bb(1) {delta = y}}\
            &= kappa(event(k), dif (delta, a, ell))\
            &=kappa_Delta (event(k), dif delta) {pi^' (event(k), delta, dif a) delta_(covariate(k-1)) (dif l) bb(1) {delta = a} \
            &+ kappa_L (event(k), delta, dif ell) delta_(treat(k-1)) (dif a) bb(1) {delta = ell} + delta_(treat(k-1),covariate(k-1)) (dif (a, l)) bb(1) {delta = y}}
    $ <eq:proofpi>
    The last equality comes from considering the various cases with a discrete mark space.
    We see that again $pi^' (t, delta, dif a)$ satisfies @eq:pi again. However, by explicitly
    integrating out various sets of @eq:proofpi, we get that $pi^' (t, delta, dif a) = P(treat(k) in dif a | event(k), status(k) = a, history(k-1))$.
]
        
// or alternatively, we can work with the random measure
// $
//     N^a (dif t times dif x) := sum_(j=1)^k  delta_(A (t)) (dif x) N^(a) (dif t)
// $
// and its compensator
// $
//     Lambda^(a) (dif t times dif x) = pi_t (dif x) Lambda^a (dif t).
// $

= Identification of the counterfactual mean outcome

Now, we let Now let $N^a (dif t times dif x) = sum_(x in cal(A)) delta_(x) (dif x) N^(a,a_j) (dif t)$.
We are interested in the outcome process $Y$ under an intervention $g^*$
which we denote by $tilde(Y)$.
Importantly, the intervention is defined as a static/dynamic intervention
$
    N^(g^*) (dif t times dif x) = pi^*_t (dif x) N^a (dif t times cal(A))
$
where $pi^*_t (dif x)$ is some kernel
that specifies the treatment decision deterministically at time $t$
in the sense that there are $history(k-1) times.o cal(B) ([0, T])$-measurable functions $g^*_k$
which return a treatment decision in $cal(A)$
such that
$
    pi^*_t (dif x) = sum_k bb(1) {event(k-1) < t <= event(k)} delta_(g^*_k (history(k-1), event(k))) (dif x),
$
This means that, critically,
$N^(g^*) (dif t times dif x)$ is also a random measure.
Note that $N^(g^*)$ has the compensator
$
    scr(L) (N) (dif t times dif x) = pi^*_t (dif x) underbrace(Lambda^a (dif t times cal(A)), =:Lambda^a (dif t)),
$
where $Lambda^a (dif t)$ is the $P$-$cal(F)_t$-compensator of $N^a (dif t times cal(A))$ --
also deemed the total $P$-$cal(F)_t$-compensator of $N^a$.
// What this means is that
// $
//     N^a ((0, t] times dif x) - Lambda^a ((0, t]) times dif x)
// $
// is a local $P$-$cal(F)_t$-martingale.
We shall write similar notations for the other components of $N$.
Let $scr(L)$ denote the $P$-$cal(F)_t$-canonical compensator of $N^(g^*)$.
However, $N^a$ generally has the compensator $Lambda^(a) (dif t times dif x) = pi_t (dif x) Lambda^a (dif t)$.
Now define the time to deviation from the treatment regime as
$
    tau^(g^*) = inf {t >= 0 | N^a ((0, t] times {x}) != N^(g^*) ((0, t] times {x}) " for some " x in cal(A)}.
$

#definition[
    Let $cal(tilde(F))_t := sigma(tilde(N)^d ((0,s]), tilde(N)^y ((0,s]), tilde(N)^a ((0,s] times {x}), tilde(N)^ell ((0,s] times {y}) | s in (0, t], x in cal(A), y in cal(L))$.
    Let $dot(Lambda)$ denote the canonical $P$-$cal(F)_t$-compensator of $N$.

    A multivariate random measure $tilde(N) = (tilde(N)^y, tilde(N)^a, tilde(N)^ell)$
    is a *counterfactual random measure* under the intervention $g^*$
    if it satisfies the following conditions.
    1. $tilde(N)^a$ has compensator $scr(L) (tilde(N))$ with respect to $cal(tilde(F))_t$.
    2. $tilde(N)^x$, has the same compensator $dot(Lambda)^x (tilde(N))$ with respect to $cal(tilde(F))_t$ for $x in {y, ell, d}$.
]

Now let $(event(k))_k$ denote the ordered event times of $N$.
The main outcome of interest is the counterfactual outcome process
$tilde(Y) := tilde(N)^y$;
and we wish to identify $mean(P) [tilde(Y)_t]$.
Also note that this definition aligns closely
with the definition of potential outcomes in discrete time
based on structural equations (@richardson2013single).

//It has been discussed in discrete time (@RobinsLongitudinal2001)
//that the g-formula is unique; however, as we shall
//see the g-formula in continuous time may not necessarily be uniquely defined.
//Specifically this may relate to conditional distributions
//in this setting not being uniquely defined.

//We also assume that we work with a version of the compensator
//such that $Lambda ({t} times {y, a} times {1, 0}) < oo$ for all $t > 0$.
//We may generally also work with a compensator $Lambda$ that fulfills conditions (10.1.11)-(10.1.13) of @last1995marked.
// Let $pi_(event(k)) (history(k-1))$ denote the treatment probability
// and let $pi^*_(event(k)) (history(k-1))$ denote the treatment probability under the intervention $g^*$

// *NOTES:*
// UI (Uniform integrability) implies zeta (t) = integral ... is uniformly integrable martingale,
// but why is integral_0^t tilde(Y)_(t) zeta (dif s) a martingale (generally a martingale)

// CAR is stronger than exchangeability => likelihood factorizes, but we do not need it to.

Now we come to a martingale result providing identification.

#theorem[
If _all_ of the following conditions hold:
- *Consistency*: $tilde(Y)_(dot) bb(1) {tau^(g^*) > dot} = Y_(dot) bb(1) {tau^(g^*) > dot} quad P-"a.s."$
- *Exchangeability*:
  Define $cal(H)_t := cal(F)_t or sigma(tilde(Y))$.
  Let $Lambda^(a, a_j) (dif t) = pi_t ({a_j}) Lambda^(a) (dif t)$ denote the $P$-$cal(F)_t$-compensator of $N^(a, a_j)$ and $Lambda^(a,a_j)_H (dif t) = pi_t^H ({a_j}) Lambda^(a)_H (dif t)$ denote the $P$-$cal(H)_t$-compensator of $N^(a, a_j)$,
  and that $(pi_t^* ({a_j}))/(pi_t^H ({a_j}))$ can be chosen càglàd, and $cal(H)_t$-predictable. We have for all $j in {1, dots, k}$ and $m in bb(N)$ that $pi_(event(m))^* ({a_j}) pi_(event(m)) ({a_j}) = pi_(event(m))^* ({a_j}) pi_(event(m))^H ({a_j})$ $P$-a.s.
  // Note: suffices for it to be in 
- *Positivity*:  
  $
      W (t) := product_(j = 1)^(N_t) (product_(i=1)^(k) ((pi^*_(event(j)) ({a_i}; history(j-1))) / (pi_(event(j)) ({a_i}; history(j-1))))^(bb(1) {treat(k) = a_i}))^(bb(1) {status(j) = a}) 
  $ <eq:rytgaard>
  is uniformly integrable $P$-$cal(F)_t$ martingale. 
  
  // Furthermore, let $K^H (t) = integral_0^t sum_(j=1)^k ((pi_s^* ({a_j}))/(pi^H_s ({a_j})) - 1) M_H^(a, a_j) (dif s)$
  // is a $P$-$cal(H)_t$-martingale and that $K^H$ is a process of *locally integrable variation*, meaning that $mean(P) [integral_0^t |d K^H (s)| ] < oo$ for all $t > 0$
  // and, moreover, that $mean(P) [integral_0^t W(s-) |dif K_s^H| ] < oo$ for $t>0$.

Further, let
$
K_t &= integral_0^t sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s)
$
Then,
$
    mean(P) [tilde(Y)_t] = mean(P) [Y_t W (t)]
$ <eq:identificationformula>
    and $W (t) = cal(E) (K)_t$ is a uniformly integrable $P$-$cal(F)_t$-martingale, where $cal(E)$ denotes the Doléans-Dade exponential (@protter2005stochastic).
] <thm:identifiabilitymartingale>

#proof[
    We shall use that the likelihood ratio solves a specific stochastic differential equation.
    First, we have that
    $
        K_t &= integral_0^t sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s) \
            &= integral_0^t sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) - sum_(j=1)^(k) ((pi_s^* ({a_j})) / (pi_s ({a_j})) - 1) Lambda^(a, a_j) (dif s) \
            &= integral_0^t sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) - sum_(j=1)^(k) (pi_s^* ({a_j}) - pi_s ({a_j})) Lambda^(a) (dif s) \
            &= integral_0^t sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s).
    $
    This shows that $W (t) = cal(E) (K)_t$.
    By exchangeability and the last equality, we also have that $K_t = integral_0^t sum_(j=1)^k ((pi_s^* ({a_j}))/(pi^H_s ({a_j})) - 1) M_(cal(H))^(a, a_j) (dif s)$,
    where $M_(cal(H))^(a,a_j) = N^(a,a_j) - Lambda_(cal(H))^(a,a_j)$ and $Lambda_(cal(H))^(a,a_j)$ denotes the $P$-$cal(H)_t$ compensator
    of $N^(a,a_j)$. Thus, since we can choose $(pi_t^* ({a_j}))/(pi_t^H ({a_j}))$ to be $cal(H)_t$-predictable and locally bounded, we see that generally $K_t$ is a local $P$-$cal(H)_t$-martingale.
    //by Lemma 7.3.20 of @cohen2015stochastic)
    // REMARK on p. 166 of protter. 
    Since $W$ is a uniformly integrable martingale on $[0, T]$, we have that
    $
        mean(P) [W(T)] = mean(P) [W(0)] = mean(P) [1] = 1
    $
    by Theorem 10.3.2 of @last1995marked.
    Hence, by Theorem 15.3.2 of @cohen2015stochastic, we have that $W$ is a $P$-$cal(H)_t$ martingale. 
    
    // We have that
    // $
    //     zeta_t := integral_0^t W(s -) sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s)
    // $ is a zero mean $P$-$cal(H)_t$-martingale by positivity.
    // From this, we see that $integral_0^t tilde(Y)_(t) zeta (dif s)$ is also a uniformly integrable $P$-$cal(H)_t$-martingale
    // by Theorem 2.1.42 of @last1995marked.
    This implies that
    $
        mean(P) [Y_t W (t)] &= mean(P) [Y_t bb(1) {tau^(g^*) > t} W(t)]  \
            &=^((**)) mean(P) [tilde(Y)_t bb(1) {tau^(g^*) > t} W (t)] \
            &= mean(P) [tilde(Y)_t W (t)] \
            &= mean(P) [tilde(Y)_t mean(P) [W(t) | cal(H)_0]] \
            &= mean(P) [tilde(Y)_t W (0)] \
            &= mean(P) [tilde(Y)_t] 
    $
    where in $(**)$ we used consistency.
]

We note some things here.
- First that @eq:rytgaard is the same likelihood ratio as in @rytgaardContinuoustimeTargetedMinimum2022.
- Also note that the Radon-Nikodym derivative is uniquely given by the second part of @thm:canonicalversion, so
  that if $pi'$ and $pi$ are the corresponding Radon-Nikodym derivatives of @thm:canonicalversion,
  then @eq:rytgaard obtained from either will be indistinguishable from each other. 
  // NOTE: Gill and robins call this uniqueness of the identifying functional. 
- Also note that in the proof, it suffices that $W$ is uniformly bounded because
  then it will also be a $P$-$cal(H)_t$-martingale
  since it is a local, bounded $P$-$cal(H)_t$-martingale.
- Note that a more general alternative to the above conditions is simply
  to assume that $W$ is a uniformly martingale on both filtrations $cal(F)_t$ and $cal(H)_t$.
- Note that alternatively, we can also require strong consistency.
  What strong consistency dictates is that $tilde(Y)_(dot and tau^(g^*)) = Y_(dot and tau^(g^*))$ $P$-a.s.
  The subtle difference is that the strict inequality is replaced by a weak one. 
  An illustration of strong consistency is presented in the figure below
  for a recurrent event outcome below. 
  
#figure(cetz.canvas(length: 1cm, {
    import cetz.draw: *

  // Set-up a thin axis style
  set-style(axes: (stroke: .5pt, tick: (stroke: .5pt)),
      legend: (stroke: none, item: (spacing: .3), scale: 80%))
    line( (0,0), (0,6), mark: (end: ">"), name: "line")
    line( (0,0), (6,0), mark: (end: ">"), name: "line")
    content((), $t$, anchor: "north-west")
    line((0, 0.3),(-0.15, 0.3))
    content((), $0$, anchor: "east")
    line((0, 2.3),(-0.15, 2.3))
    content((), $1$, anchor: "east")
    line((0, 4.3),(-0.15, 4.3))
    content((), $2$, anchor: "east")

    line( (0.1,0.3), (1.2,0.3), mark: (end: "o"), stroke: (paint: blue))
    line( (1.2,2.3), (3.6,2.3), mark: ( end: "o"), stroke: (paint: blue))
    line( (3.6,2.3), (5,2.3), mark: (fill: blue), stroke: (dash: "dashed", paint: blue))
    line( (3.5,4.3), (5,4.3), mark: (fill: blue, start: "o"), stroke: (paint: blue))
    line( (2.7, 0.15), (2.7, -0.15))
    content((), $tau^(g^*)$, anchor: "north")
    
    line( (8,0), (8,6), mark: (end: ">"), name: "line")
    content((), $A(t)$, anchor: "east")
    line( (8,0), (14,0), mark: (end: ">"), name: "line")
    content((), $t$, anchor: "north-west")
    line((8, 2.3),(7.85, 2.3))
    content((), $1$, anchor: "east")
    line((8, 0.3),(7.85, 0.3))
    content((), $0$, anchor: "east")

    line( (8.1,2.3), (10.7,2.3), mark: ( end: "o"), stroke: (paint: blue))
    line( (10.6,0.3), (13,0.3), mark: (fill: blue, start: "o"), stroke: (paint: blue))
    line( (10.7, 0.15), (10.7, -0.15))
    content((), $tau^(g^*)$, anchor: "north")
}), caption: [The figure illustrates the consistency condition for the potential outcome framework for single individual.
    The left panel shows the potential outcome process $tilde(Y) (t)$ (dashed) and the observed process $Y (t)$ (solid).
    The right panel shows the treatment process $A(t)$. At time $tau^(g^*)$, the treatment is stopped and the processes
    may from some random future point diverge from each other.
    In this case, the treatment is beneficial for the user, as it would have prevented another recurrent event from happening. 
]) <fig:potentialoutcome>

// *NOTE:* Would be very nice for positivity stated in terms of $K$ only.
// Note that assuming that $K$ is uniformly integrable and a $P$-$cal(F)_t$ martingale
// implies that it is of class D with respect to $cal(F)_t$. If we also had that it was of class D
// with respect to $cal(H)_t$, then we could state positivity for the observed data, but not the unobserved data.
// Maybe it would be possible to do something directly with the event times.

In @rytgaardContinuoustimeTargetedMinimum2022,
both an exchangeability condition and a
positivity condition are presented,
but no proof is given that these conditions
imply that their target parameter is identified.
Our proposal shows that under the conditions of @thm:identifiabilitymartingale,
the g-formula given in @rytgaardContinuoustimeTargetedMinimum2022
causally identifies the counterfactual mean outcome
under the assumption that the other martingales are orthogonal
to the treatment martingale.
Lemma 1 of @ryalenPotentialOutcomes then gives the desired target parameter.
Note that this is weaker than the assumptions in @rytgaardContinuoustimeTargetedMinimum2022,
as they implicitly require that _all_ martingales are orthogonal
due to their factorization of the likelihood. This is because
$cal(E) (X) cal(E) (Y) = cal(E) (X + Y)$ if and only if $[X, Y] = 0$.
This can be seen by applying Theorem 38, p. 130 of @protter2005stochastic
and using that the stochastic exponential solves a specific stochastic differential equation.
We do not provide a more concise statement here.

#theorem("g-formula")[
    Let, further, $Q = W(T) dot P$ denote the probability measure defined by the likelihood ratio $W(T)$ given in @eq:rytgaard.
    Under positivity, then
    1. The $Q$-$cal(F)_t$ compensator of $N^a (dif t times dif x)$ is $pi^*_t (dif x) Lambda^a (dif t)$.
    2. The $Q$-$cal(F)_t$ compensator of $N^x$ is $Lambda^x$ for $x in {y, ell}$. // addition should be zero; by Jacods formula for likelihood ratios
] <thm:gformula>

#proof[
    First note that for a local $cal(F)_t$-martingale $X$ in $P$, we have
    $
        integral_0^t 1/(W_(s -)) dif chevron.l W, X chevron.r_s^P = chevron.l K, X chevron.r_t^P
    $ <eq:girsanov1>
    since we have that $W_t = 1 + integral_0^t W_(s -) dif K_s$; whence
    $
        chevron.l W, X chevron.r_t = chevron.l 1, X chevron.r_t + chevron.l W_(-) bullet K, X chevron.r_t = W_(t -) bullet chevron.l K, X chevron.r_t
    $ 
    With $X= M^(a, x)$, we find
    $
        chevron.l K, M^(a, x) chevron.r_t^P &= integral_0^t sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) dif chevron.l M^(a, a_j), M^(a, x) chevron.r_s^P \
            &= integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) dif chevron.l M^(a, x) chevron.r_s^P + sum_(j != x) integral_0^t ((pi_s^* (a_j))/(pi_s (a_j)) - 1) dif chevron.l M^(a, a_j), M^(a, x) chevron.r_s^P \
            &= integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) pi_s (x) Lambda^a (dif s)  - integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) Delta (pi (x) Lambda^a)_s pi_s (x) Lambda^a (dif s) \
            &quad - sum_(j!= x) integral_0^t ((pi_s^* (a_j))/(pi_s (a_j)) - 1) Delta (pi (x) Lambda^a)_s pi_s (a_j) Lambda^a (dif s) \
            &= integral_0^t (pi_s^* (x) - pi_s (x)) Lambda^a (dif s)  - sum_(j) integral_0^t (pi_s^* (a_j) - pi_s (a_j)) Delta (pi (x) Lambda^a)_s Lambda^a (dif s) \
            &= integral_0^t (pi_s^* (x) - pi_s (x)) Lambda^a (dif s).
    $ <eq:girsanova>
    Girsanov's theorem (Theorem 41, p. 136 of @protter2005stochastic)
    together with @eq:girsanov1 and @eq:girsanova
    gives that 
    $
        N^a (dif t times dif x) - pi_t (dif x) Lambda^a (dif t) - (pi_t^* (dif x) - pi_t (dif x)) Lambda^a (dif t) = N^a (dif t times dif x) - pi_t^* (dif x) Lambda^a (dif t)
    $
    is a $Q$-$cal(F)_t$-local martingale. The second statement follows by noting that
    $
        [M^(y), K]_t &= integral_0^t Delta N_t^y sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) N^(a, a_j) (dif s) - integral_0^t Delta Lambda^y (s) sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) M^(a, a_j) (dif s) \
    $
    where we apply the trick with adding and subtracting the treatment compensators in the second term.
    The first term is zero because no two counting processes jump at the same time.
    The second term is a local martingale. This implies $chevron.l M^(y), K chevron.r_t^P = 0$.
    For $x=ell$ the argument is the same.
]

= Comparison with @ryalenPotentialOutcomes

It is natural to ask oneself: how does
our conditions
relate to the ones of @ryalenPotentialOutcomes?
The condition of consistency is the same.
However, the exchangeability condition and
the positivity condition are different in general.
// We compare exclusively the exchangeability conditions
// as the positivity condition is not really interesting.
The overall point of the present subsection is to argue that
the identification formula in @ryalenPotentialOutcomes cannot generally
identify the causal estimand, but that there is, in general,
a different causal interpretation behind that identification formula.
Moreover, we argue that under structural, albeit unrestrictive assumptions,
the two causal estimands are the same.

First, let $bb(N)_t^a = bb(1) {tau^(g^*) <= t}$
and let $bb(L)_t$ denote its $P$-$cal(F)_t$-compensator.
Then, exchangeability in @ryalenPotentialOutcomes is that 

- *Exchangeability*: 
  Define $cal(H)_t := cal(F)_t or sigma(tilde(Y))$.
  The $P$-$cal(F)_t$ compensator for $bb(N)^a$ is also the $P$-$cal(H)_t$ compensator.

Let $tilde(W) (t) := (cal(E) (-bb(N)^a)_t) / (cal(E) (-bb(L)^a)_t) = cal(E) (bb(K)^a)_t$
and $tilde(Q) := tilde(W) (T) dot P$,
where $bb(K)^a_t = - integral_0^t 1/(1- Delta bb(L)^a_s ) (bb(N)^a (dif s) - bb(L)^a (dif s))$.
If additionally positivity as described in @ryalenPotentialOutcomes holds,
then
$
    mean(P) [tilde(Y)_t] = mean(P) [tilde(W) (t) Y_t].
$ <eq:ryalenIdentification>

== A different intervention yielding the same identification formula as @ryalenPotentialOutcomes

Suppose that we represent $N$ as the multivariate counting process
$N = (N^y, N^d, N^(ell,l_1), dots, N^(ell,l_(d_l)), N^(a,a_1), N^(a,a_0))$,
where, for simplicity, we take $cal(A) = {a_0,a_1}$.
We are interested in the effect of staying on treatment $a_1$,
which prevents $N^(a,a_0)$-events.
From a philosophical point of view there is a difference in actually constitutes complete data can be different.
The intervention we have discussed earlier would include _all_ treatment visitation times
as complete data. This intervention, however, would only include the treatment visitation times
where treatment $a_1$ is assigned to the patient. 

This is a predictable intervention; however, the
intervention that is formulated previously is an optional intervention, in general. 
With canonical compensators, we see that for the potential outcome process for this intervention
$
    tilde(Lambda)^(x) (dif t) &= dot(Lambda)^(x) (tilde(N)') (dif t), x != a,a_0, a,a_1 \
    tilde(Lambda)^(a,a_1) (dif t) &= pi_t (tilde(N)', {a_1}) dot(Lambda)^(a) (tilde(N)') (dif t) \
    tilde(Lambda)^(a,a_0) (dif t) &= 0 
$
However, because $pi_t (tilde(N)', {a_1}) != 1$, it is not guaranteed
that $mean(P) [tilde(Y)_t] = mean(P) [tilde(Y)'_t]$. @ryalenPotentialOutcomes gives conditions
under which there exists such a potential outcome process; for instance if $chevron.l M^(a_0), M^(x) chevron.r^P_s = 0$
for $x!= a,a_0$ in this situation.
On the other hand, note that $tau^(g^*) = inf {t > 0 | N^(a,a_1) (t) != N^(a,a_1) (t) + N^(a,a_0) (t) or N^(a, a_0) (t) != 0} = inf {t>0 |N^(a,a_1) (t) != 0}$.
Thus, the identification formulae for $mean(P) [tilde(Y)_t]$ and
$mean(P) [tilde(Y)'_t]$ are actually the same for two _different_ interventions;
and the exchangeability conditions are the same -- we replace $tilde(Y)$ with $tilde(Y)'$ here. 
//However, as we shall see, these need not be the same even under the orthogonal martingales assumption.
We argue that there are situations for observed in which the exchangeability condition for $tilde(Y)$ can fail,
but as we have argued this cannot occur for $tilde(Y)'$ under the assumption of orthogonal martingales.

// Intuitively, I think this one is more related to coarsening at random with censoring

// - *Positivity*:
//   $
//       tilde(W) (t) := (cal(E) (-bb(N)^a)_t) / (cal(E) (-bb(L)^a)_t) = cal(E) (bb(K)^a)_t
//   $
//   is uniformly integrable, where $bb(K)^a_t = - integral_0^t 1/(1- Delta bb(L)^a_s ) (bb(N)^a (dif s) - bb(L)^a (dif s))$.
//   Furthermore, $bb(K)^a$ is a process of *locally integrable variation*
//   and a $P$-$cal(F)_t$-martingale. 


== Example with no time-varying confounding and one treatment event showing that the identification formulas may be different
#figure(diagram(spacing: (9mm, 12mm), debug: false, node-stroke: 0.5pt, node-inset: 10pt, label-size: 7pt, {
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
    edgemsm(novisit, treat_visit, [$pi_t (a_1) lambda_t^a$])
    edgemsm(novisit, treat_visit_2, [$(1-pi_t (a_1)) lambda_t^a$])
    
    edgemsm(novisit, death, [$lambda_t^y$])
    edgemsm(treat_visit, death, [$lambda_t^y (a_1, s)$])
    edgemsm(treat_visit_2, death, [$lambda_t^y (a_0, s)$])
    }

    msm_function(offset: (0,0), scale_text: 70%)
    let tint(c) = (stroke: c, fill: rgb(..c.components().slice(0,3), 5%))
    //node(label: [#align(top + right)[$P$]], enclose: ((-2.7, -0.3), (2.5, 3.3)),..tint(green))
    //msm_function(offset: (-1.5, 5), scale_text: 70%)
    //msm_function(offset: (2, 5), scale_text: 70%)
}), caption: [A multi-state model allowing one visitation time for the treatment with the possible treatment values 0/1. ])
<fig:multi-state>

Consider a simple example where $N^a (t) <= 1$ for all $t$,
we observe $N = (N^y, N^(a,a_0), N^(a,a_1))$, and that people are assigned treatment at $t=0$ as in a randomized trial. 
We consider the intervention $pi^*_t (a_1) = 1$ for all $t$.
Suppose that $(N^y, N^(a,a_0), N^(a,a_1))$ has compensator
$
    Lambda^y (dif t) (P) &= bb(1) {t <= event(1)} lambda_t^y dif t + bb(1) {event(1) < t <= event(2)} lambda_t^y (treat(1), event(1)) dif t, \
    Lambda^(a,a_j) (dif t) (P) &= bb(1) {t <= event(1)} pi_t (a_j) lambda_t^a dif t, j=0,1.
$
with respect to its natural filtration.
Is it then possible to construct a potential outcome fulfilling consistency and exchangeability
in the sense of @ryalenPotentialOutcomes such that $mean(P) [tilde(Y)_t] = mean(P) [tilde(W) (t) Y_t]$
and when is it possible?
// In $P$, note that
// $
//     mean(P) [Y_t] &= mean(P) [N^y (t)] \
//         &= mean(P) [bb(1) {event(1) <= t, status(1) = y} + bb(1) {status(1) = a, treat(1) = 1, event(2) <= t, status(2) = y} + bb(1) {status(1) = a, treat(1) = 0, event(2) <= t, status(2) = y}]\
//         &= integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^y dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) pi_s ({a_1}) lambda_s^(a) integral_s^t exp(- integral_s^v lambda_u^y ) dif u) lambda_v^y dif v dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) (1-pi_s ({a_1}))lambda_s^(a,a_0) integral_s^t exp(- integral_s^v lambda_u^y ) dif u) lambda_v^y dif v dif s \
// $

First note that in in $Q$ (defined in @thm:gformula), we have
$
    Lambda^y (dif t) (Q) &= Lambda^y (dif t) (P), \
    Lambda^(a,a_0) (dif t) (Q) &= 0 dif t, \
    Lambda^(a,a_1) (dif t) (Q) &= Lambda^a (dif t) (P)
$
However, in $tilde(Q)$ (the change of measure in @ryalenPotentialOutcomes), we have
$
    Lambda^y (dif t) (tilde(Q)) &= Lambda^y (dif t) (P) \ //(lambda_t^y dif t-0)/(1-0), \
    Lambda^(a,a_0) (dif t) (tilde(Q)) &= 0 dif t, \ //(0-0)/(1-0) \
    Lambda^(a,a_1) (dif t) (tilde(Q)) &= pi_t ({a_1}; P) Lambda^a (dif t) (P)//(lambda_t^a dif t - (1-pi_(t and tau^(g^*))(a_1)) lambda^a_(t and tau^(g^*)) dif t)/(1-0) = pi_(t and tau^(g^*))(a_1) lambda^a_(t and tau^(g^*)) dif t = pi_(t)(a_1) lambda^a_(t) dif t.
$
since $tau^(g^*) = oo$ almost surely in $tilde(Q)$.

First, we identify when one can do this in this example.

=== Example showing the identification formulae are the same under a local independence condition
Suppose that $lambda_t^y (1, s) = lambda^y_t$ for $s < t$ (in $P$).
Then, we show $mean(Q) [Y_t] = mean(tilde(Q)) [Y_t]$ by showing that $mean(tilde(Q)) [Y_t]$
does not depend on the Radon-Nikodym derivative $pi_t ({a_1})$.
Thus,
$
    mean(tilde(Q)) [Y_t] &= mean(tilde(Q)) [N^y (t)] \
        &= mean(tilde(Q)) [bb(1) {event(1) <= t, status(1) = y} + bb(1) {status(1) = a, treat(1) = 1, event(2) <= t, status(2) = y}]\
        &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_(u)(a_1) lambda_u^(a)) dif u) lambda_s^y dif s \
        &#h(1.5cm) + integral_0^t exp(- integral_0^s (lambda_u^y + pi_(u)(a_1) lambda_u^(a)) dif u) pi_(s)(a_1) lambda_s^(a) integral_s^t exp(- integral_s^v lambda_u^y (1, s) dif u) lambda_v^y (1, s) dif v dif s \
        &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_(u)(a_1) lambda_u^(a) dif u)) lambda_s^y dif s \
        &#h(1.5cm) + integral_0^t exp(- integral_0^s (lambda_u^y + pi_(u)(a_1) lambda_u^(a)) dif u) pi_(s)(a_1) lambda_s^(a) (1-exp(- integral_s^t lambda_u^y (1, s) dif u)) dif s \
        &= 1- exp(- integral_0^t (lambda_u^y + pi_(u)(a_1) lambda_u^(a)) dif u) - integral_0^t exp(- integral_0^s (lambda_u^y +pi_(u)(a_1) lambda_u^(a)) dif u) pi_(s)(a_1) lambda_s^a dif s \
        &#h(1.5cm)+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_(u)(a_1) lambda_u^(a)) dif u) pi_(s)(a_1) lambda_s^(a)  (1-exp(- integral_s^t lambda_u^y (1, s) dif u)) dif s \
        &= 1- exp(- integral_0^t (lambda_u^y + pi_(u)(a_1) lambda_u^(a)) dif u) \
        &#h(1.5cm) - integral_0^t exp(- integral_0^s (lambda_u^y + pi_(u)(a_1) lambda_u^(a)) dif u) pi_(s)(a_1) lambda_s^(a) exp(- integral_s^t lambda_u^y (1, s) dif u) dif s \
        &=^((!)) 1- exp(- integral_0^t (lambda_u^y + pi_(u)(a_1) lambda_u^(a)) dif u) - exp(-integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_(u)(a_1) lambda_u^(a)) dif u) pi_(s)(a_1) lambda_s^(a) dif s \
        &= 1- exp(- integral_0^t (lambda_u^y + pi_(u)(a_1) lambda_u^(a)) dif u) - exp(-integral_0^t lambda_u^y dif u) (1-exp(- integral_0^t lambda_u^(a) pi_(u)(a_1) dif u)) \
        &= 1 - exp(- integral_0^t lambda_u^y dif u)
$ <eq:examplediff>
In (!), we apply the stated local independence condition.

=== Example showing the identification formulae are different
In the observed data, take
$
    pi_t ({a_1}) &= pi in (0,1), \
    lambda_t^y &= lambda^y \
    lambda_t^a &= lambda^a \
    lambda^y_t (1, s) &= lambda^(y,2) != lambda^y
$
and further pick them so that $lambda^a+lambda^y-lambda^(y,2) != 0$.
Then, we have from the fourth last equality of @eq:examplediff,
$
    mean(Q) [Y_t] &= 1-exp(- (lambda^y + lambda^(a)) t) - integral_0^t exp(- (lambda^y + lambda^(a)) s) lambda^(a) exp(- lambda^(y,2) (t-s)) dif s \
        &= 1-exp(- (lambda^y + lambda^(a)) t) - lambda^(a) exp(- lambda^(y,2) t)/(lambda^a+lambda^y-lambda^(y,2)) (1-exp(- (lambda^a + lambda^y-lambda^(y,2)) t))
$
Replacing $lambda^(a)$ with $pi lambda^(a)$ yields $mean(tilde(Q)) [Y_t]$, i.e.,
$
    mean(tilde(Q)) [Y_t] = 1-exp(- (lambda^y + pi lambda^(a)) t) - pi lambda^(a) exp(- lambda^(y,2) t)/(pi lambda^a+lambda^y-lambda^(y,2)) (1-exp(- (pi lambda^a + lambda^y-lambda^(y,2)) t))
$
Taking
$
    pi &= lambda^a = 0.5 \
    lambda^y &= 0.2 \
    lambda^(y,2) &= 0.8
$
with $t=3$, we have
$
    mean(Q) [Y_t] = 1-exp(-(0.2+0.5) 3)-0.5 exp(-(0.8)3)/(0.5+0.2-0.8)(1-exp(-(0.5+0.2-0.8)3)) approx 0.72
$
while
$
    mean(tilde(Q)) [Y_t] = 1-exp(-(0.2+0.5 times 0.5) 3)-0.5 times 0.5 exp(-(0.8)3)/(0.5 times 0.5+0.2-0.8)(1-exp(-(0.5 times 0.5+0.2-0.8)3)) approx 0.62
$
However by the argument in @section:construct, we can construct the potential outcome process $tilde(Y)$
fulfilling consistency and exchangeability as in @thm:identifiabilitymartingale,
so we actually have that $mean(Q) [Y_t] = mean(P) [tilde(Y)_t]$, but $mean(tilde(Q)) [Y_t] != mean(P) [tilde(Y)_t]$.

// Therefore,
// $
//     mean(tilde(Q)) [Y_t] &= mean(tilde(Q)) [N^y (t)] \
//         &= mean(tilde(Q)) [bb(1) {event(1) <= t, status(1) = y} \
//             &+ bb(1) {status(1) = a, treat(1) = 1, event(2) <= t, status(2) = y}]\
//         &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) lambda_s^y dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) lambda_s^y dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times (1-exp(- integral_s^t lambda_u^y dif u))  dif s \ 
// $

// === Example with time-varying confounding
// We now consider a more natural example, where the difference is due to time-varying confounding.
// Suppose that $(N^y, N^(a,a_0), N^(a,a_1), N^ell)$ has compensator
// $
//     Lambda^y (dif t) (P) &= lambda_t^y dif t, \
//     Lambda^ell (dif t) (P) &= lambda_t^ell dif t, \
//     Lambda^(a,a_j) (dif t) (P) &= pi_t (a_j) lambda_t^a dif t, j=0,1.
// $
// Påls functional can be written as
// $
//     &integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) lambda_s^y dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) (lambda_v^y + lambda^ell_v integral_v^t exp(- integral_v^w lambda_u^y (ell_2; v) dif u) lambda^y_w (ell_2; v) dif w) dif v dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u) \
//         &quad times (lambda_v^y (ell_1 ; s) + pi_v (a_1) (ell_1 ; s) lambda_v^(a) (ell_1 ; s) integral_v^t exp(- integral_v^w lambda_u^y (ell_1 ; s) dif u) lambda^y_w (ell_1; s) dif w) dif v dif s \
//         &=integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) lambda_s^y dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) (lambda_v^y + lambda^ell_v (1- exp(- integral_v^t lambda_u^y (ell_2; v) dif u))) dif v dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u) \
//         &quad times (lambda_v^y (ell_1 ; s) + pi_v (a_1) (ell_1 ; s) lambda_v^(a) (ell_1 ; s) (1-exp(- integral_v^t lambda_u^y (ell_1 ; s) dif u)) dif v dif s \
// $
// Can we conclude this result does not depend on $pi_t (a_1)$?
// Now, note that
// $
//     &integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) lambda_s^y dif s \
//         &=[- exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u)]_0^t - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) (pi_s (a_1) lambda_s^(a) + lambda_s^ell) dif s \
//         &= 1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) (pi_s (a_1) lambda_s^(a) + lambda_s^ell) dif s \    
// $
// Conclude that the previous is equal to
// $
//     &1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) \
//         &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) dif s \
//         &-integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(- integral_s^t (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))) dif s \
//     &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
//         &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u) \
//         &quad times pi_v (a_1) (ell_1 ; s) lambda_v^(a) (ell_1 ; s) exp(- integral_v^t lambda_u^y (ell_1 ; s) dif u) dif v dif s \
//     &=1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) \
//         &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) dif s \
//         &-integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(- integral_s^t (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))) dif s \
//     &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
//         &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
//         &quad times exp(-integral_s^t lambda_u^y (ell_1; s) dif u) (1-exp(- integral_s^t (pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u)) dif s \
// $
// $
//         &1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) \
//         &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) dif s \
//     &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
//             &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y (ell_1; s) dif u) dif s \
//     &=1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//     &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
//         &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y (ell_1; s) dif u) dif s 
// $
// We now apply integration by parts to the last two terms.
// Let $h(v, s) = exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u)$.

// Obtain
// $
//     &integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) integral_s^t h(v,s) dif v dif s \
//         &=[- exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v]^(s=t)_(s=0) \
//         &- integral_0^t (- exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) (partial)/(partial s) integral_s^t h(v,s) dif v) dif s \
//         &- integral_0^t ((lambda_s^y + lambda_s^ell) exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v) dif s \
//         &= integral_0^t h(v,s) dif v + integral_0^t (exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) (partial)/(partial s) integral_s^t h(v,s) dif v) dif s \
//         &- integral_0^t ((lambda_s^y + lambda_s^ell) exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v) dif s \
//                 &= integral_0^t h(v,s) dif v - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) h(s,s) dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t (partial)/(partial s) h(v,s) dif v dif s \
//         &- integral_0^t ((lambda_s^y + lambda_s^ell) exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v) dif s \
//         &= integral_0^t h(v,s) dif v - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda^ell_v exp(- integral_s^t lambda_u^y (ell_2; s) dif u) dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t (partial)/(partial s) h(v,s) dif v dif s \
//         &- integral_0^t ((lambda_s^y + lambda_s^ell) exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v) dif s \
//         &= integral_0^t h(v,s) dif v - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda^ell_v exp(- integral_s^t lambda_u^y (ell_2; s) dif u) dif s \
// $
// Since it is assumed that $lambda_u^y (ell_2; s) = lambda_u^y (ell_1; s)$,
// we finally have that
// $
//     1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) - integral_0^t h(v,s) dif v
// $
// which does not depend on $pi_t (a_1)$.
// These conclusions should generalize and work under an orthogonal martingales assumption. 

== More general argument (sketch)
#theorem[
    Suppose that $(N^(a,a_1), dots, N^(a,a_j)) arrow.r.struck N^(-a) (dot and tau^(g^*))$ (local independence understood in terms of the compensator).
    Here, $N^(-a)$ denotes is every other counting process that is not a treatment counting process.

    Then,
    $
        mean(tilde(Q)) [Y_t] = mean(Q) [Y_t]
    $
]
#proof[
One can get the canonical compensators from the two measures $Q$ and $tilde(Q)$
from $P$ via @thm:gformula and Lemma ? in @ryalenPotentialOutcomes. Here,
we see that $Q$ and $tilde(Q)$ agree on the canonical compensator for every component that is not
a treatment component. We can now induce measures $Q'$ and $tilde(Q)'$ restricting
the measures to every other component than the treatment component (can be done explicitly)
and consider its smaller generated natural filtration of the new marked point process.
Under a local independence statement, the compensators under smaller filtration and the original
filtration are the same. However, this means that the canonical compensators in $Q'$
and $tilde(Q)'$ will be the same and hence the distribution of $(Y_t)_(t in [0, T])$ will be the same
in the two induced measures and hence in the original probability measures.
]

Another example where they are the same is when the total treatment process
is $cal(F)_t$-predictable:
Now, we calculate
$
    bb(K)_t^a &= -integral_0^t 1/(1 - Delta bb(L)_s^a) dif (bb(N)_s^a - bb(L)^a_s) \
        &= -integral_0^(t and tau^(g^*)) sum_(x in cal(A)) (1-pi^*_s (x)) 1/(1 - sum_(y in cal(A)) (1-pi^*_s (y)) pi_s (y)) (N^(x) (dif s) - pi_s (x) macron(N)^a (dif s)) \
        &= -integral_0^(t and tau^(g^*)) sum_(x in cal(A)) (1-pi^*_s (x)) 1/(sum_(y in cal(A)) pi^*_s (y) pi_s (y)) (N^(x) (dif s) - pi_s (x) macron(N)^a (dif s)) \
        &= integral_0^(t and tau^(g^*)) sum_(x in cal(A)) (pi^*_s (x))/(pi_s (x)) (N^(x) (dif s) - pi_s (x) macron(N)^a (dif s)) \
        &quad - integral_0^(t and tau^(g^*)) 1/(sum_(y in cal(A)) pi^*_s (y) pi_s (y)) (sum_(x in cal(A)) N^(x) (dif s) - sum_(x in cal(A)) pi_s (x) macron(N)^a (dif s)) \
        &= integral_0^(t and tau^(g^*)) sum_(x in cal(A)) (pi^*_s (x))/(pi_s (x)) (N^(x) (dif s) - pi_s (x) macron(N)^a (dif s)) \
        &quad - integral_0^(t and tau^(g^*)) 1/(sum_(y in cal(A)) pi^*_s (y) pi_s (y)) (macron(N)^a (dif s) - macron(N)^a (dif s)) \
        &= integral_0^(t and tau^(g^*)) sum_(x in cal(A)) (pi^*_s (x))/(pi_s (x)) (N^(x) (dif s) - pi_s (x) macron(N)^a (dif s)) \
        &= integral_0^(t and tau^(g^*)) sum_(x in cal(A)) ((pi^*_s (x))/(pi_s (x))-1) (N^(x) (dif s) - pi_s (x) macron(N)^a (dif s)) \
        &= K_t^*
$


// Does $N^x -|> N^y$ when $N^x$ predictable always hold? No

// #theorem[
//     Consider the static intervention with $g^* (history(k-1), event(k)) = 1$ for all $k$.
//     and $cal(A) = {0, 1}$.
//     Suppose consistency for $tilde(Y)_t$ as in @thm:identifiabilitymartingale.
//     Let $pi^cal(H)_t (1)$, $pi^cal(F)_t (1)$
//     denote the Radon-Nikodym derivatives of $Lambda^(a, 1)$
//     with respect to $Lambda^(a)$
//     in the filtrations $cal(H)_t$ and $cal(F)_t$, respectively.
//     Similarly, let $Lambda^(a, cal(H))$, $Lambda^(a, cal(F))$
//     denote the compensators of $N^a$ in the filtrations $cal(H)_t$
//     and $cal(F)_t$, respectively.
//     Suppose that a version of $pi_s^cal(F))$ exists such that
//     $
//         pi_s^cal(F) (1, omega) < 1
//     $ <eq:nonperfectcompliance>
//     for all $s in [0, T]$ and $omega in Omega^*$ with $P(Omega^*) = 1$.
//     Also, suppose that strong consistency holds for $tilde(N)_t^a$, i.e.,
//     $
//         tilde(N)_dot^a bb(1) {tau^(g^*) >= dot} = N_dot^a bb(1) {tau^(g^*) >= dot} quad P-"a.s."
//     $
//     Let $cal(H)_t$ denote the initial expansion of
//     $cal(F)_t$ with $sigma(tilde(N)_dot^a, tilde(Y)_dot)$.
//     If the compensator of $bb(N)^a$ in the filtration $cal(H)_t$ is 
//     $cal(F)_t$-predictable, then $N^a (dot and tau^(g^*))$
//     is $cal(F)_t$-predictable. 
// ]
// #proof[

// // Then, we have that
// // $
// //     mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t]
// // $
// // by @thm:identifiabilitymartingale if $W_dot$ is a uniformly integrable martingale.

// // However, note that
// // $
// //     bb(L)_t^a &= integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a) (dif s) \
// //         &= integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s).
// // $ <eq_bbL>
// // is a $cal(H)_t$-compensator of $bb(N)^a$.
// // Here, we use that the compensator of $bb(1) {bb(N)_(s-)^a = 0} N^a (dif s)$
// // is $bb(1) {bb(N)_(s-)^a = 0} N^a (dif s)$ itself in the filtration $cal(H)_t$.
// // If $tilde(W)_t = cal(E) (-bb(K)^a)_t$ is such that it is a $P$-$cal(H)_t$-martingale (integrability conditions),
// // then it will be a $P$-$cal(F)_t$-martingale as well,
// // where $bb(K)^a_t = integral_0^t 1/(1 - Delta bb(L)_s^a) dif bb(M)_s^a$,
// // by the stated argument since the compensator of $bb(N)^a$ in $cal(H)_t$
// // is also $cal(F)_t$-adapted.
// // Nonetheless, @eq_bbL in itself almost never be $cal(F)_t$-predictable,
// // leading to possible issues -- also about the existence of such a $bb(L)^a$
// // if treatment compensator is continuous in $cal(F)_t$, then it will almost never be able to the above?
// // Conclude that if this is the case, then exchangeability in Påls setting can never hold.

// Note that, under the stated conditions
// $
//         integral_0^dot bb(1) {s <= tau^(g^*)} N^(a) (dif s)
// $
// is a $cal(H)_t$-predictable process.
// Therefore, it is its own compensator in $cal(H)_t$.
// Now note that
// $
//     bb(L)^cal(H)_dot &= integral_0^dot  (1-pi^(cal(H))_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(H)) (dif s) \
//         &= integral_0^dot  (1-pi^(cal(H))_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s).
// $
// On the other hand,
// $
//     bb(L)_dot^cal(F) &= integral_0^dot  (1-pi^(cal(F))_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(F)) (dif s) 
// $
// Conclude that if $bb(L)^cal(H)$ is indistinguishable from $bb(L)^cal(F)$,
// then
// $
//     (1-pi^(cal(H))_dot (1)) bb(1) {dot <= tau^(g^*)} Delta N^a (dot) = (1-pi^(cal(F))_dot (1)) bb(1) {dot <= tau^(g^*)} Delta Lambda^(a,cal(F)) (dot).
// $
// Therefore,
// $
//     bb(L)^cal(H)_dot = integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
// $
// on a set up to $P$-indistinguishability.
// If this were $cal(F)_t$-predictable, then
// $
//     bb(L)^cal(H)_dot &= integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
//         &= integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} M^(a, cal(F)) (dif s) + integral_0^t  (1-pi^(cal(F))_s (1)) Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(F)) (dif s) 
// $
// Conclude that since
// $integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} M^(a, cal(F)) (dif s)$
// is a difference of two non-decreasing processes, and hence of finite variation,
// a local martingale,
// by p. 115 of @protter2005stochastic that 
// $
//     integral_0^dot (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} N^(a) (dif s) = integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(F)) (dif s).
// $
// Then, we have that $bb(1) {dot <= tau^(g^*)} Delta Lambda^(a,cal(F)) (T^a_(k)) = -1$ by @eq:nonperfectcompliance
// for all jump times $T_(k)^a$ of $N^a$.
// However, we also have that
// $
//     bb(1) {s <= tau^(g^*)} Delta Lambda^(a,cal(F)) (s) = 0
// $
// whenever $s$ is not a jump time of $N^a$ by @eq:nonperfectcompliance.
// This shows the statement for the discrete part of the compensator.
// For the continuous part, we are now able to conclude from these two parts that
// $
//     integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} lambda^(a, cal(F)) (s) dif s = 0
// $
// from which we conclude that
// $
//         bb(1) {s <= tau^(g^*)} lambda^(a, cal(F)) (s) = 0
// $
// for almost all $s$ with respect to the Lebesgue measure
//     and almost all $omega in Omega^(**)$ with $P(Omega^(**)) = 1$.
// However, these two restrictions exactly mean that $bb(1) {s <= tau^(g^*)} N^a (dif s)$
// is a $cal(F)_t$-predictable process.
// ]

= Variations of the sequential exchangeability criteria yielding the same identification formula 

We now provide a sequential representation
of the exchangeability condition.
It aligns closely with the postulated exchangeability condition
in @rytgaardContinuoustimeTargetedMinimum2022;
however, notably on the conditioning set, we include
the $k$'th event time, which is not included in @rytgaardContinuoustimeTargetedMinimum2022.
The sequential condition is a bit unusual in the sense that
we do not condition on the strict history.
We also provide an equivalent statement for the martingale condition.
// We conclude that if we have independent marking for the treatment
// process, the condition in @rytgaardContinuoustimeTargetedMinimum2022
// is sufficient for causal identification. 

#theorem[
    Suppose consistency and positivity holds as in @thm:identifiabilitymartingale.
    Then, we have
    $
        mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t],
    $
    for all $t in [0, T]$, if for $k in bb(N)$
    and $t in [0, T]$ it holds that
    $
        tilde(Y)_t perp bb(1) {treat(k) = g^* (history(k-1), event(k))} | cal(F)^(g^*)_(event(k-1)), event(k) <= t, status(k) = a,
    $
    where
    $
        cal(F)^(g^*)_event(k) = sigma(covariate(k), status(k), bb(1) {treat(k) = g_k^* (history(k-1), event(k))), dots, bb(1) {treat(0) = g_0^*(covariate(0))}, covariate(0))
    $
] <thm:sequentialcriterion>

#proof[
    We see immediately that,
    $
        &integral W_(s-) bb(1) {event(m) < s < event(m+1) and t} dif K_s \
            &= W_(event(m)) integral bb(1) {event(m) < s < event(m+1) and t} dif K_s \
            &= W_(event(m)) bb(1) {event(m) < t} (sum_j (pi^*_(event(m)) ({a_j})) / (pi_(event(m)) ({a_j})) - 1) N^(a, a_j) (event(m+1) and t) \
            &= W_(event(m)) bb(1) {event(m) < t} ((bb(1) {treat(m) = g_m^* (history(m-1), event(m))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) N^(a, a_j) (event(m+1) and t) 
    $
    By consistency and positivity, the desired result is equivalent to 
    $
        sum_(m=0)^(oo) mean(P) [integral W_(s-) bb(1) {event(m) < s < event(m+1) and t} dif K_s tilde(Y)_t] = 0
    $
    by Lemma 4 of @ryalenPotentialOutcomes, so
    $
        &sum_(m=0)^(oo) mean(P) [integral W_(s-) bb(1) {event(m) < s < event(m+1) and t} dif K_s tilde(Y)_t] \
            &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} ((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m), event(m+1))}))- 1) N^(a, a_j) (event(m+1) and t) tilde(Y)_t] \
            &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                &quad times mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) tilde(Y)_t | history(m), event(m+1) <= t, status(k) = a]] \
            &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                &quad times mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) | history(m), event(m+1) <=, status(k) = a] \
                &quad times mean(P) [tilde(Y)_t | history(m), event(m+1) <= t, status(k) = a]] \
                        &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                            &quad times mean(P) [
                                mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) | history(m), event(m+1), status(m+1)=a] \
                                    &quad quad | history(m), event(m+1) <= t, status(k) = a] \
                &quad times mean(P) [tilde(Y)_t | history(m), event(m+1) <= t, status(k) = a]] \
                    &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) times (1- 1) mean(P) [tilde(Y)_t | history(m), event(m+1) <= t, status(k) = a]] \
            &= 0.
    $
]

Now we compare a sequential criterion to the full exchangebility statement. 

#lemma[
    Note that 
    $
        (tilde(Y)_t)_(t in [0, T]) perp bb(1) {treat(k) = g^* (history(k-1), event(k))} | cal(F)^(g^*)_(event(k-1)), event(k), status(k) = a,
    $
    for all $k in bb(N)$ if and only if $W(t)$ is $cal(F)_t$-measurable. 
]
#proof[
    "If": Follows from the previous result.
    
    Conversely, suppose that $W(t)$ is $cal(F)_t$-measurable.
    Then, we have
    $
        &W(event(k)) / W(event(k-1)) bb(1) {tau^(g^*) > event(k-1), event(k-1) < oo} \
            &= ((bb(1) {treat(k) = g^* (history(k-1), event(k))})
            /(P(treat(k) = g^* (history(k-1), event(k)) | history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T]))))^(bb(1) {status(k+1) = a}) bb(1) {tau^(g^*) > event(k-1), event(k-1) < oo}
    $ is $history(k)$-measurable. Hence
    $
        &bb(1) {treat(k) = g^* (history(k-1), event(k)), status(k) = a} \
            &quad times 1/P(treat(k) = g^* (history(k-1), event(k)) | history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T])) bb(1) {tau^(g^*) > event(k-1), event(k-1) < oo} \
        &= bb(1) {treat(k) = g^* (history(k-1), event(k)), status(k) = a} W(event(k)) / W(event(k-1)) bb(1) {tau^(g^*) > event(k-1), event(k-1) < oo} \
            &=^((*)) f_k (event(k), status(k), treat(k), covariate(k), dots, treat(0), covariate(0)) \
            &= bb(1) {treat(k) = g^* (history(k-1), event(k)), status(k) = a} f_k (event(k), a, g^* (history(k-1), event(k)), covariate(k), dots, treat(0), covariate(0)) \
    $
    In $(*)$, we use that that the previous line is $history(k)$-measurable.
    Take the conditional expectation on both sides given $history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T])$ to conclude that
    $
        &P(treat(k) = g^* (history(k-1), event(k)) | history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T])) bb(1) {tau^(g^*) > event(k-1), event(k-1) < oo, status(k) = a} \
            &= 1/(f_k (event(k), status(k), treat(k), covariate(k), dots, treat(0), covariate(0))) bb(1) {tau^(g^*) > event(k-1), event(k-1) < oo, status(k) = a}
    $
    is $sigma(history(k-1),event(k))$-measurable whenever the probability is non-zero.
    This suffices for the sequential condition.
    //Note: Are versions adapted here? Yes because the kernel must be equal to the probabilities at the stopping times 
]

= On the existence of counterfactual processes fulfilling consistency and exchangeability <section:construct>

It is natural to ask oneself whether there exist counterfactual processes
for any given law of $N$ such that consistency and exchangeability holds.
This question was already posed by @RobinsLongitudinal2001 in the discrete time setting.
If this does not hold, then, certainly, we would implicitly be imposing
restrictions on the observed data law of $N$. As the theorem below shows,
we can assume that such counterfactual processes do in fact exist,
as they cannot be ruled out by the distribution of observed data.

#theorem[
    For any law of $N$, we can construct a probability space,
    wherein a counterfactual process $tilde(N)$ and $N$ exists
    such that (strong) consistency and exchangeability (in the sense of @thm:sequentialcriterion) holds.
    Here (strong) consistency means that
    $
        tilde(N)_t bb(1) {tau^(g^*) >= t} = N_t bb(1) {tau^(g^*) >= t} quad P-"a.s."
    $
    which implies that
    $
        integral_0^t bb(1) {s <= tau^(g^*)} dif tilde(N)_t  = integral_0^t bb(1) {s <= tau^(g^*)} dif N_t,
    $
    or
    $
        tilde(N)_(dot and tau^(g^*)) = N_(dot and tau^(g^*))
    $
] <thm:existencecounterfactuals>

#proof[
    // Do we need to check the compensator definition?
    We provide an argument somewhat analogous to the one given in Section 6 of @RobinsLongitudinal2001.

    *Construction of counterfactual process*
    
    First, we let $(event(k), status(k), treat(k), covariate(k))_(k in NN)$ denote the marked point process
    corresponding to $N$ and $(treat(0), covariate(0))$ be the initial values of the treatment and covariate process.
    First, we generate $covariate(0)$ from its marginal distribution.
    Next, for $a_0 in cal(A)$, we generate $(L^(a_0)(T_((1))^(a_0)),T_((1))^(a_0), Delta^(a_0)_((1))) tilde covariate(1), event(1), status(1) | treat(0) = a_j, covariate(0)$
    (for each value of $a_0$, these can be generated independently).
    Next, for each combination of $a_0 in cal(A)$ and $a_1 in cal(A)$ where $Delta_((1))^(a_0) = a$, we generate
    $
        &(L^(a_0, a_1)(T_((2))^(a_0, a_1)), T_((2))^(a_0, a_1), Delta^(a_0, a_1)_((2))) \
            &tilde covariate(2), event(2), status(2) | covariate(1) = l_1, treat(1) = a_1, event(1) = t_1, status(1) = s_1, treat(0) = a_0, covariate(0)
    $
    where $(l_1, t_1, s_1) = (L^(a_0)(T_((1))^(a_0)),T_((1))^(a_0), Delta^(a_0)_((1)))$
    for $Delta^(a_0)_((1)) != y$ and $T^(a_0)_((1)) < T$. If $Delta^(a_0)_((1)) = y$, put $(L^(a_0, a_1)(T_((2))^(a_0, a_1)), T_((2))^(a_0, a_1), Delta^(a_0, a_1)_((2))) = (Ø, oo, Ø)$.
    Continue in this manner to define $(L^(a_0, dots, a_k)(T_((k))^(a_0, dots, a_1)), T_((k))^(a_0, dots, a_k), Delta^(a_0, dots, a_k)_((k)))$
    for all $k in NN$.
    
    Then, we define $tilde(N)$ by the marked point process.
    Let as a shorthand $g_0^*(L(0)) = g_0^+$, $g_1^* = g_1^* (L(0), g_0^*, T_((1))^(g_0^*))$
    and so on. 
    Let
    $
        &(tilde(L)(tilde(T)_1), tilde(A)(tilde(T)_1), tilde(T)_1, tilde(Delta)_1) = (L^(g_0^*)(T_((1))^(g_0^*)), g_1^* bb(1) {Delta^(g_0^* = a}} + g_0^*  bb(1) {Delta^(g_0^*) != a}, T_((1))^(g_0^*), Delta^(g_0^*))
    $
    and continue in this manner for all $k in NN$.

    *Construction of factual process*

    Next, we construct the observed data process $N$.
    We can generate the $A$'s independently from all other considered random variables.
    Generate $treat(0)$ from its conditional distribution given $covariate(0)$.
    Then, let 
    $
        (covariate(1), event(1), status(1)) = (L^(treat(0))(T_((1))^(treat(0))), T_((1))^(treat(0)), Delta^(treat(0))_((1))).
    $
    Then, again, generate $treat(1)$ from its conditional distribution given $history(0), event(1), status(1) = a$.
    Afterwards, let
    $
        (covariate(2), event(2), status(2)) = (L^(treat(0), treat(1))(T_((2))^(treat(0), treat(1))), T_((2))^(treat(0), treat(1)), Delta^(treat(0), treat(1))_((2))).
    $
    Continue in this manner for all $k in NN$.
    
    *Consistency*

    Next, we show consistency.
    Define
    $
        tilde(N)^x_t = sum_k bb(1) {T_((k))^(g_0^*, dots, g_(k-1)^*) <= t, Delta^(g_0^*, dots, g^'_(k-1))_((k)) = x}
    $
    and
    $
        N^x_t= sum_k bb(1) {event(k) <= t, status(k) = x}
    $
    Now note that
    $
        N^x_t bb(1) {tau^(g^*) >= t} &= sum_k bb(1) {event(k) <= t, status(k) = x} bb(1) {tau^(g^*) > t} \
            &= sum_k bb(1) {event(k) <= t, status(k) = y, treat(j) = g_j^*, forall j < k} \
            &= sum_k bb(1) {T_((k))^(g_0^*, dots, g_(k-1)^*) <= t, Delta^(g_0^*, dots, g^'_(k-1))_((k)) = x, treat(j) = g_j^*, forall j < k} \
            &= sum_k bb(1) {T_((k))^(g_0^*, dots, g_(k-1)^*) <= t, Delta^(g_0^*, dots, g^'_(k-1))_((k)) = x} bb(1) {tau^(g^*) > t} \
            &= tilde(N)^x_t bb(1) {tau^(g^*) > t}.
    $
    as desired.
    
    *Exchangeability*

    By construction, we then have
    $
        (tilde(N)_t)_(t in [0, T]) perp treat(k) | cal(F)^g_(event(k-1)), event(k), status(k) = a
    $
    which suffices for exchangeability by @thm:sequentialcriterion.
    
    *Distribution*

    It is immediate the $(N_t)_(t in [0, T])$ has the right distribution
    since the described procedure simply generates the desired distribution.

    Now we check the counterfactual outcome process.
    By Theorem 4.1.11 (ii) of @last1995marked,
    we get the compensator
    $
        mu(dif (l, a, delta, t)) := sum_k bb(1) {tilde(T)_(k-1) < t <= tilde(T)_k} (P((tilde(L)(tilde(T)_k), tilde(A)(tilde(T)_k), tilde(Delta)_k, tilde(T)_k) in dif (l, a, delta, t) | tilde(cal(F))_(tilde(T)_(k-1))))/P(tilde(T)_k >= t | tilde(cal(F))_(tilde(T)_(k-1)))
    $
    with respect to the filtration $tilde(cal(F))_t$; the natural filtration of the counterfactual process.
    By integrating over the respective sets, we find that for every non-treatment component that the compensator
    is the same as in the observed data. We find that
    $
        mu(cal(L) times {a_j} times {a} times (0, t]) &= integral_((0, t]) sum_k bb(1) {tilde(T)_(k-1) < t <= tilde(T)_k} (P(tilde(A)(tilde(T)_k) = a_j, tilde(Delta)_k = a, tilde(T)_k in dif t | tilde(cal(F))_(tilde(T)_(k-1))))/P(tilde(T)_k >= t | tilde(cal(F))_(tilde(T)_(k-1))) \
            &= integral_((0, t]) sum_k bb(1) {tilde(T)_(k-1) < t <= tilde(T)_k}  \
            & #h(1.5cm) times P(tilde(A)(tilde(T)_k) = a_j | tilde(Delta)_k = a, tilde(T)_k = t, tilde(cal(F))_(tilde(T)_(k-1))) (P(tilde(Delta)_k = a, tilde(T)_k in dif t | tilde(cal(F))_(tilde(T)_(k-1))))/P(tilde(T)_k >= t | tilde(cal(F))_(tilde(T)_(k-1))) \
            &= integral_((0, t]) sum_k bb(1) {tilde(T)_(k-1) < t <= tilde(T)_k} bb(1) {a_j = g_j^*} (P(tilde(Delta)_k = a, tilde(T)_k in dif t | tilde(cal(F))_(tilde(T)_(k-1))))/P(tilde(T)_k >= t | tilde(cal(F))_(tilde(T)_(k-1))) \
            &= integral_((0, t]) pi^*_s ({a_j}) Lambda^a (dif s),
    $
    and the proof is complete. 
]

== Full exchangeability and standard exchangeability
Consider a basic example where we observe $N^y$ (primary event), $N^d$ (competing event),
$N^a$, and $A(t)$, but not necessarily the baseline confounder $L$.
We can let
$
    O &= (event(1), status(1), treat(1), event(2), status(2)) \
    tilde(O) &= (event(1), status(1), 1, tilde(T)_2, tilde(Delta)_2)
$
Then $tilde(N)_t^x = bb(1) {event(1) <= t, status(1) = x} + bb(1) {tilde(T)_2 <= t, tilde(Delta)_2 = x}$.
Then, we can have
$
    P(treat(1) = 0|event(1), status(1) = a, (tilde(N)_t^y)_(t in [0, T])) = P(treat(1) = 0|event(1), status(1) = a),
$
but 
$
    P(treat(1) = 0|event(1), status(1) = a, (tilde(N)_t^y, tilde(N)_t^d)_(t in [0, T]) != P(treat(1) = 0|event(1), status(1) = a).
$

We provide an example showing this when the event times have densities. First note 
$
    &P(treat(1) = 0|event(1) = t, status(1) = a, tilde(T)_2 = t_2, tilde(Delta)_2 = x, L=l) \
        &= (p_((event(1), status(1), tilde(T)_2, tilde(Delta)_2)  | treat(1), L) (t, a, t_2, x | 0, l) P(treat(1) = 0 | L = l)) /(p_(event(1), status(1), tilde(T)_2, tilde(Delta)_2 | L) (t, a, t_2, x| l)) \
        &= (p_((tilde(T)_2, tilde(Delta)_2) | event(1), status(1), treat(1), L) (t_2, x | t, a, 0, l) p_(event(1), status(1)| treat(1), L) (t, a | 0, l) P(treat(1) = 0 | L = l)) /(p_(tilde(T)_2, tilde(Delta)_2 | event(1), status(1), L) (t_2, x| t, a,  l) p_(event(1), status(1) | L) (t, a | l)) \
$
Then, we have
$
    &P(treat(1) = 0|event(1) = t, status(1) = a, tilde(T)_2 = t_2, tilde(Delta)_2 = x) \
        &= sum_(l=0,1) P(treat(1) = 0|event(1) = t, status(1) = a, tilde(T)_2 = t_2, tilde(Delta)_2 = x, L=l) \
        &quad P(L = l | event(1) = t, status(1) = a, tilde(T)_2 = t_2, tilde(Delta)_2 = x) \
        &= sum_(l=0,1) P(treat(1) = 0|event(1) = t, status(1) = a, tilde(T)_2 = t_2, tilde(Delta)_2 = x, L=l) \
        &quad (p(tilde(T)_2 = t_2, tilde(Delta)_2 = x | event(1) = t, status(1) = a, L = l) p(event(1) = t, status(1) = a | L = l) P (L = l))/(p(event(1) = t, status(1) = a) p(tilde(T)_2 = t_2, tilde(Delta)_2 = x | event(1) = t, status(1) = a))
$
This is not a function of $t_2$ and $x$ if
$
    p_(tilde(T)_2, tilde(Delta)_2 | event(1), status(1), treat(1), L) (t_2, x | t, a, 0, l) = p_(tilde(T)_2, tilde(Delta)_2 | event(1), status(1)) (t_2, x | t, a)
$
but otherwise it is generally. Let $tilde(T)^y$ denote the event time of $tilde(N)^y$.
Then, likewise for the other statement,
$
    P(treat(1) = 0|event(1) = t, status(1) = a, tilde(T)^y = t_2) \
$
is not a function of $t_2$ if
$
    p_(tilde(T)^y | event(1), status(1), treat(1), L) (t_2 | t, a, 0, l) = p_(tilde(T)^y| event(1), status(1)) (t_2 | t, a)
$
Now note that
$
    P(tilde(T)^y <= t | event(1), status(1) = a, treat(1) = 0, L) = P(tilde(T)_2 <= t, tilde(D)_2 = y | event(1), status(1) = a, treat(1) = 0, L)
$
and
$
    P(tilde(T)^y = oo | event(1), status(1) = a, treat(1) = 0, L) = P(tilde(D)_2 = d | event(1), status(1) = a, treat(1) = 0, L)
$
However, it is possible to construct the distribution of the second event times in this way. For example we can let $tilde(Delta)_2$ be independent of $treat(1)$ and $L$,
then let $tilde(T)_2$ be dependent on $A$ and $L$ given $tilde(Delta)_2 = d$, but not given $tilde(Delta)_2=y$.
We could for instance use the procedure described in @thm:existencecounterfactuals.

= Right-censoring
Now suppose that in addition to the processes we observe, we also observe a component $N^c (t)$
which counts whether or not the subject has dropped out of the study at time $t$.
$tau^C$ denotes the first time at which this process is non-zero. 
Now consider the weight process,
$
    W (t) = W^(g^*) (t) W^c (t)
$ <eq:generalW>
where $W^(g^*)$ denotes the previously studied weight process given in @eq:rytgaard
and
$
    W^c (t) = (bb(1) {tau^C > t}) / (cal(E) (-Lambda^c)_t) = cal(E) (- integral_0^dot 1/(1-Delta Lambda^c (s)) dif (N^c - Lambda^c))_t := cal(E) (bb(K)^c)_t
$
where $Lambda^c$ denotes the $cal(F)_t$-compensator of $N^c$.
We will assume that $chevron.l M^c, M^x chevron.r^P_s = 0$ for all $x != c$.
This impies that
$
    W(t) = cal(E) (K^* + bb(K)^c)_t
$
This now yields the following g-formula.


#theorem("g-formula")[
    Let, further, $Q = W(T) dot P$ denote the probability measure defined by the likelihood ratio $W(T)$ given in @eq:generalW.
    Under positivity, then
    1. The $Q$-$cal(F)_t$ compensator of $N^a (dif t times dif x)$ is $pi^*_t (dif x) Lambda^a (dif t)$.
    2. The $Q$-$cal(F)_t$ compensator of $N^x$ is $Lambda^x$ for $x in {y, ell_1, dots, ell_k}$.
    3. The $Q$-$cal(F)_t$ compensator of $N^c$ is $0$.
]

#proof[
    By the same logic as the original theorem, we find
    $
        integral_0^t 1/(W(s-)) dif chevron.l W, X chevron.r_s^P =  chevron.l K^*, X chevron.r_t +  chevron.l bb(K)^c, X chevron.r_t
    $
    Since $chevron.l bb(K)^c, X chevron.r_t = - integral_0^t 1/(1-Delta Lambda^c (t)) dif chevron.l M^c, X chevron.r_s$,
    we find for $X!= M^c$, the same result as in the previous theorem since $chevron.l M^c, M^x chevron.r^P_s = 0$ for all $x != c$.
    On the other hand, for $X=M^c$, we find
    $
        integral_0^t 1/(W(s-)) dif chevron.l W, X chevron.r_s^P =  chevron.l bb(K)^c, X chevron.r_t = - integral_0^t 1/(1-Delta Lambda^c (t)) dif chevron.l M^c chevron.r_s = - Lambda^c (t)
    $
    which shows the $N^c$'s compensator under $Q$ is zero. 
]

= More general exchangeability conditions

We now consider more general exchangeability conditions.
#theorem[
    Let $Q_kappa = cal(E) (kappa)_T dot P$ where $kappa$ is a local $P$-$cal(F)_t$ martingale
    with $Delta kappa_t >= -1$.
    If
    1. Consistency holds as in @thm:identifiabilitymartingale.
    2. $cal(E) (kappa)_t cal(E) (-bb(N)^a)_t = cal(E) (kappa)_t$ for all $t in [0, T]$ $P$-a.s.
    3. $Q_kappa$ is a uniformly integrable $P$-$cal(F)_t$-martingale and $P$-$cal(H)_t$-martingale, where $cal(H)_t = cal(F)_t or sigma(tilde(Y))$.
    Then,
    $
        mean(P) [tilde(Y)_t] = mean(P) [Y_t cal(E) (kappa)_t]
    $
] <thm:identifiabilitygeneral>
#proof[
    The proof is the same as in @thm:identifiabilitymartingale -- mutatis mutandis.
]

We provide an equivalent characterization of condition 2 in the above theorem
which gives direct interpretability of that condition
in the sense that it should induce a probability measure $Q_kappa$
under which the time to deviation from the treatment regime is infinite almost surely.

#lemma[
    $Q_kappa (tau^(g^*) = oo) = 1$ if and only if $cal(E) (kappa)_t cal(E) (-bb(N)^a)_t = cal(E) (kappa)_t$ for all $t in [0, T]$ $P$-a.s.
]
#proof[
    "If" part:
    $
        Q_kappa (tau^(g^*) = oo) &= mean(P) [cal(E) (kappa)_T bb(1) {tau^(g^*) = oo}] \
            &= mean(P) [lim_(t -> oo) cal(E) (kappa)_t bb(1) {tau^(g^*) > t}] \
            &= mean(P) [lim_(t -> oo) cal(E) (kappa)_t] \
            &= mean(P) [cal(E) (kappa)_T] = 1.
    $
    "Only if" part:
    Suppose that $Q_kappa (tau^(g^*) = oo) = 1$.
    Then for every $t in [0, T]$,
    $
        mean(P) [cal(E) (kappa)_t bb(1) {tau^(g^*) > t}] &= mean(P) [mean(P) [cal(E) (kappa)_T | cal(F)_t] bb(1) {tau^(g^*) > t}] \
            &= mean(P) [cal(E) (kappa)_T bb(1) {tau^(g^*) > t}] \
            &= Q(tau^(g^*) > t) \
            &= 1.
    $
    On the other hand,
    $mean(P) [cal(E) (kappa)_t] = mean(P) [mean(P) [cal(E) (kappa)_T | cal(F)_t]] = mean(P) [cal(E) (kappa)_T] = 1$.
    Conclude that
    $
        mean(P) [cal(E) (kappa)_t (1 - bb(1) {tau^(g^*) > t})] = 0.
    $
    The integrand on the left hand side is non-negative and so it must be zero $P$-a.s.
]

#lemma[
    Let $kappa_t$ be a (local) martingale with $Delta kappa_t >= -1$
    and $Delta kappa_t^* > -1$ if $t < tau^(g^*)$. Then, 
$
    W_t^* := cal(E) (kappa)_t = cal(E) (kappa)_t cal(E) (- bb(N)^a)_t 
$
    if and only if $Delta kappa_(tau^(g^*)) = -1$ whenever $tau^(g^*) < oo$.
] <thm:kappa>
#proof[
    Using the well-known formula $cal(E) (X) cal(E) (Y) = cal(E) (X + Y + [X, Y])$,
    we have
    $
        cal(E) (kappa) = cal(E) (kappa - bb(N)^a - [kappa, bb(N)^a])
    $
    This holds if and only if
    $
        1 + integral_0^t W_(t -) dif kappa_s = 1 + integral_0^t W_(t -) dif (kappa_s - bb(N)^a_s - [kappa, bb(N)^a]_s)
    $
    if and only if
    $
        integral_0^t W_(t -) Delta kappa_s dif bb(N)^a_s = - integral_0^t W_(t -) dif bb(N)^a_s 
    $
    and this is
    $
        bb(1) {tau^(g^*) <= t} W_(tau^(g^*) -) Delta kappa_(tau^(g^*)) = - bb(1) {tau^(g^*) <= t} W_(tau^(g^*) -)
    $
    By assumption, $W_(tau^(g^*) -) > 0$ (looking at the explicit solution of the SDE) and so the above holds if and only if
    $
        bb(1) {tau^(g^*) <= t} Delta kappa_(tau^(g^*)) = - bb(1) {tau^(g^*) <= t}
    $
    Taking $t -> oo$ gives the desired result. On the other hand, if the result holds then,
    $
        bb(1) {tau^(g^*) <= t} Delta kappa_(tau^(g^*)) &= bb(1) {tau^(g^*) <= t} bb(1) {tau^(g^*) < oo} Delta kappa_(tau^(g^*)) \
            &=bb(1) {tau^(g^*) <= t} bb(1) {tau^(g^*) < oo} (-1) = - bb(1) {tau^(g^*) <= t}
    $
] 

= Uniqueness

// If there are two solutions (mine and theirs), they may be an infinite number of solutions
// due to convexity

Now, we consider only $kappa$'s of the form 
$
    kappa (t) = integral sum_(x in cal(A)) bb(1) {s <= t} tilde(h) (s, x) M^(a, x) (dif s)
$
with $tilde(h) (s, x)$ $P$-$cal(H)_t$ predictable
with the restriction stated in the above theorem
and $M^(a,x)$ are $P$-$cal(H)_t$ local martingales. 
We make this restriction as any reasonable exchangeability conditions
should be placed on treatment and not anything else.

// #theorem[
//     Let $cal(H)_t^a$ denote the filtration of $cal(F)_t$ with the initial enlargement of
//     $tilde(Y)$ and $tilde(N)^a$. Suppose that  $kappa$ is of finite variation
//     and that consistency holds for the total treatment process, i.e.,
//     $
//         tilde(N)^a_(dot and tau^(g^*)) = N^a_(dot and tau^(g^*)) P-"a.s."
//     $
//     Then,
//     $
//         cal(E) (K^*)_t = cal(E) (kappa)_t
//     $
//     for every $t in [0, T]$ and every local $H^a_t$-martingale $kappa$ with $Delta kappa_t < -1$ if $t < tau^(g^*)$.
// ]
// #proof[
//     See proof of the next theorem in the predictable case. Do not know if it can be generalized for more than two treatment options.
//     // By @thm:kappa, we have
//     // $
//     //     -1 &= sum_(x in cal(A)) tilde(h) (tau^(g^*), x) Delta M^(a, x) (tau^(g^*)) \
//     //         &= sum_(x in cal(A)) tilde(h) (tau^(g^*), x) (1-pi^*_(tau^(g^*)) (x) - pi_(tau^(g^*)) (x))
//     // $
//     // which gives
//     // $
//     //     sum_(x in cal(A)) tilde(h) (tau^(g^*), x) (1-pi^*_(tau^(g^*)) (x)) &= -1 + sum_(x in cal(A)) tilde(h) (tau^(g^*), x) pi_(tau^(g^*)) (x) \
//     //         &= -1 + sum_(x in cal(A)) tilde(h) (tau^(g^*), x) (1-pi^*_(tau^(g^*)) (x)) pi_(tau^(g^*)) (x) + sum_(x in cal(A)) tilde(h) (tau^(g^*), x) pi^*_(tau^(g^*)) (x) pi_(tau^(g^*)) (x) 
//     // $
//     // which gives
//     // $
//     //     sum_(x in cal(A)) tilde(h) (tau^(g^*), x) (1-pi^*_(tau^(g^*)) (x)) (1-pi_(tau^(g^*)) (x)) &= -1 + sum_(x in cal(A)) tilde(h) (tau^(g^*), x) pi^*_(tau^(g^*)) (x) pi_(tau^(g^*)) (x) \
//     //         &= sum_(x in cal(A)) pi^*_(tau^(g^*)) (x)(tilde(h) (tau^(g^*), x) pi_(tau^(g^*)) (x) -1)
//     // $
//     // Gives $sum_(x in cal(A)) tilde(h) (tau^(g^*), x) (1-pi^*_(tau^(g^*)) (x)) (sum_(y in cal(A)) pi_(tau^(g^*)) (y) pi^*_(tau^(g^*)) (y))$.
//     // Then
//     // $
//     //     kappa_t &= integral_0^t sum_(x in A) tilde(h) (s, x) M^x (dif s) \
//     //         &= integral_0^t sum_(x in A) tilde(h) (s, x) N^x (dif s) - integral_0^t sum_(x in A) tilde(h) (s, x) Lambda^x (dif s) \
//     //         &=integral_0^t sum_(x in A) (1-pi_s^* (x))tilde(h) (s, x) N^x (dif s) + integral_0^t sum_(x in A) pi_s^* (x) tilde(h) (s, x) N^x (dif s) - integral_0^t sum_(x in A) tilde(h) (s, x) Lambda^x (dif s) \
//     //         &=integral_0^t sum_(x in A) (pi_s (x) tilde(h) (s,x) + pi_s^* (x) (tilde(h) (s, x)-1) )N^x (dif s) - integral_0^t sum_(x in A) tilde(h) (s, x) Lambda^x (dif s) \
//     //         &=integral_0^t sum_(x in A) ((pi_s (x) + pi_s^* (x)) tilde(h) (s, x) - pi_s^* (x) ) M^x (dif s) - integral_0^t sum_(x in A) (tilde(h) (s, x) (1 - pi_s (x)  -pi_s^* (x)) + pi_s^*(x)) Lambda^x (dif s) \
//     // $
//     // Does not quite work there is more than two treatment options.
//     // Problem is that there is an indicator for which part deviated, which is not in general predictable.     
// ]

// #theorem[
//     Let $kappa_t = integral sum_(x in cal(A)) bb(1) {s <= t} tilde(h) (s, x) M^(a, x) (dif s)$
//     for some $P$-$cal(F)_t$-predictable process $tilde(h) (s, x)$
//     and that $Q_kappa (tau^(g^*) = oo) = 1$.
//     Suppose that $Delta kappa_t >= -1$ and $Delta kappa_t^* > -1$ if $t < tau^(g^*)$
//     and that $cal(E) (kappa)_t$ is a uniformly integrable $P$-$cal(F)_t$-martingale.
//     Suppose that $cal(A) = {a_0, a_1}$ and that $pi_t^* (a_1) = 1$.
//     Then any $kappa$ with $tilde(h) (s, a_1)$ a $P$-$cal(F)_t$-predictable process and
//     $
//         tilde(h) (s, a_0) =bb(1) {s <= tau^(g^*)} (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s))
//     $
//     will satisfy the condition 2. of @thm:identifiabilitygeneral. Moreover, this solution is unique in the sense that
//     whenever $integral_0^t tilde(h) (s, a_0) M^(a, a_0) (dif s)$ is of finite variation,
//     this is equal to
//     $
//         integral_0^t bb(1) {s <= tau^(g^*)} (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) M^(a, a_0) (dif s).
//     $
//     Conclude that, under regularity conditions,
//     $
//         cal(E) (kappa)_t &= 1 + integral_0^t cal(E) (kappa)_(s -) bb(1) {s <= tau^(g^*)} (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) M^(a, a_0) (dif s) \ 
//             &+ integral_0^t cal(E) (kappa)_(s -) tilde(h) (s, a_1) M^(a, a_1) (dif s)
//     $
//     are all the solutions to condition 2. of @thm:identifiabilitygeneral,
//     where $tilde(h) (s, a_1)$ is any $P$-$cal(F)_t$-predictable process, ensuring that $cal(E) (kappa)_t$ is a uniformly integrable $P$-$cal(F)_t$-martingale.
// ]
// #proof[

// //We also suppose that $Delta Lambda^(a, x)_t < 1$.
// //This happens for example if $Delta Lambda^a_t < 1$.
// The above theorem gives that we must have
// $
//     Delta kappa_(tau^(g^*)) = sum_(x in cal(A)) tilde(h) (tau^(g^*), x) Delta M^(a, x)_(tau^(g^*)) = -1
// $
// on the event that $tau^(g^*) < oo$.
// Suppose that $cal(A) = {a_0, a_1}$
// and that $pi_t^* (a_1) = 1$.
// In this case, we can write the equation above as
// $
//     h(tau^(g^*), a_1) (0 - pi_(tau^(g^*)) (a_1) Delta Lambda^(a)_(tau^(g^*))) + h(tau^(g^*), a_0) (1 - (1- pi_(tau^(g^*)) (a_1)) Delta Lambda^(a)_(tau^(g^*))) = -1
// $
// or
// $
//     (h(tau^(g^*), a_0) - h(tau^(g^*), a_1)) pi_(tau^(g^*)) (a_1) Delta Lambda^(a)_(tau^(g^*)) + h(tau^(g^*), a_0) (1 - Delta Lambda^(a)_(tau^(g^*))) = -1
// $
// We consider various cases:
// - Absolutely continuous case: $Delta Lambda^(a) equiv 0$.
// - $macron(N)^a$ is $cal(F)_t$-predictable.
// - Jump times for $macron(N)^a$ are discrete.
// - General case.

// == Absolutely continuous case <sec:absolutely_continuous_case>
// In this case, conclude that $h(tau^(g^*), a_0) = -1$.
// However, nothing else can be said about $h(tau^(g^*), a_1)$
// as the equation does not place any other restrictions than
// it being predictable.
// We can, however, conclude that $integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) = integral_0^(t and tau^(g^*)) (-1) M^(a, a_0) (dif s) = - bb(N)^(a) (t) + bb(L)^(a) (t)$
// whenever that integral happens to be of finite variation.
// To see this, note that
// $
//     integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) &= integral_0^(t and tau^(g^*)) h(s, a_0) N^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) h(s, a_0) Lambda^(a, a_0) (dif s) \
//         &= integral_0^(t and tau^(g^*)) (-1) N^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) h(s, a_0) Lambda^(a, a_0) (dif s) \
//         &= integral_0^(t and tau^(g^*)) (-1) M^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) (h(s, a_0) + 1) Lambda^(a, a_0) (dif s),
// $
// meaning that $integral_0^(t and tau^(g^*)) (h(s, a_0) + 1) Lambda^(a, a_0) (dif s)$
// is of finite variation, a local martingale, predicable and hence constant (and thus zero)
// by Theorem 15, p. 115 of @protter2005stochastic.

// == $macron(N)^a$ is $cal(F)_t$-predictable
// Im this case, $Delta Lambda_t^a = Delta macron(N)_t^a$
// which is 1 at $t = tau^(g^*)$.
// Therefore,
// $
//     (h(tau^(g^*), a_0) - h(tau^(g^*), a_1)) pi_(tau^(g^*)) (a_1) = -1
// $
// or
// $
//     h(tau^(g^*), a_0) = h(tau^(g^*), a_1) - 1/(pi_(tau^(g^*)) (a_1))
// $
// Thus, we have
// $
//     K^(h)_t &= integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) + integral_0^(t and tau^(g^*)) h(s, a_1) M^(a, a_1) (dif s) \
//         &= integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) (h(s, a_1)) M^(a, a_0) (dif s) + integral_0^(t and tau^(g^*)) (h(s, a_1)) M^(a) (dif s) \
//         &= integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s) \
//         &= integral_0^(t and tau^(g^*)) (- 1/(pi_(s) (a_1))) N^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) Lambda^(a, a_0) (dif s) \
//         &= integral_0^(t and tau^(g^*)) (- 1/(pi_(s) (a_1))) M^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) ((h(s, a_0)-h(s, a_1)) + 1/(pi_(s) (a_1))) Lambda^(a, a_0) (dif s) \
// $
// Assuming that $integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s)$ is of finite variation,
// we have that $integral_0^(t and tau^(g^*)) ((h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s) = integral_0^(t and tau^(g^*)) (- 1/(pi_(s) (a_1))) M^(a, a_0) (dif s)$.
// We conclude that $K^(h)_t$ if $integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s)$ is of finite variation
// does not depend on the choice of $h$.
// Therefore, the stochastic exponential $cal(E) (K^(h))_t$ does not depend on the choice of $h$ either,
// and we may conclude that $cal(E) (K^(h))_t = cal(E) (K)_t$.

// == General case
// Suppose that $(1-pi_t (a_1)) Delta Lambda^(a)_(t) < 1$ for all $t > 0$.
// Otherwise, an argument similar to the one we will give will split into cases.

// We have that
// $
//     &(h(tau^(g^*), a_0) - h(tau^(g^*), a_1)) pi_(tau^(g^*)) (a_1) Lambda^(a) ({tau^(g^*)}) bb(1) {Lambda^(a) ({tau^(g^*)}) > 0} \
//         &quad + h(tau^(g^*), a_0) (1 - Lambda^(a) ({tau^(g^*)})) bb(1) {Lambda^(a) ({tau^(g^*)}) > 0} \
//         &quad + h(tau^(g^*), a_0) (bb(1) {Lambda^(a) ({tau^(g^*)}) = 0}) = -1
// $

// By the same argument as in the absolutely continuous case,
// we have that
// $
//     &integral_0^(t and tau^(g^*)) h(s, a_0) bb(1) {Lambda^(a) ({s}) = 0} M^(a, a_0) (dif s) \
//         &= - integral_0^(t and tau^(g^*)) bb(1) {Lambda^(a) ({s}) = 0} M^(a,a_0) (dif s) \
//         &= - bb(N)^(a) (t) bb(1) {Lambda^(a) ({tau^(g^*)}) = 0} + bb(L)^(a, c) (t),
// $
// where $bb(L)^(a, c)$ is the continuous part of $bb(L)^a$.
// Next whenever $Lambda^(a) ({tau^(g^*)}) > 0$, we find
// $
//     h(tau^(g^*), a_0) = (- 1 + h(tau^(g^*), a_1) pi_(tau^(g^*)) (a_1) Delta Lambda^(a)_(tau^(g^*))) / (1 - (1-pi_(tau^(g^*)) (a_1)) Delta Lambda^(a)_(tau^(g^*)))
// $
// Therefore, it will again be the case that
// $
//     &integral_0^(t and tau^(g^*)) h(s, a_0) bb(1) {Lambda^(a) ({s}) > 0} M^(a, a_0) (dif s) \
//         &= integral_0^(t and tau^(g^*)) (- 1 + h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1 - (1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) bb(1) {Lambda^(a) ({s}) > 0} M^(a, a_0) (dif s) \
// $
// Conclude that
// $
//     &integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) \
//         &= integral_0^(t and tau^(g^*)) ((- 1 + h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1 - (1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) bb(1) {Lambda^(a) ({s}) > 0} - bb(1) {Lambda^(a) ({s}) = 0}) M^(a, a_0) (dif s) \
//         &= integral_0^(t and tau^(g^*)) (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) M^(a, a_0) (dif s),
// $
// and $h(dot,a_1)$ freely chosen, predictable satisfying some integrability criteria.
// Interestingly, this means that the stochastic exponential $cal(E) (K^(h))_t$ will depend on the choice of $h$ in general,
// but only through $h(s, a_1)$ which can be freely chosen.
// ]

Now, we consider the more interesting question is there a different
probability measure $Q_kappa != Q$ such that
$
    mean(Q_kappa) [Y_t] = mean(Q) [Y_t]
$ <eq:uniqueness>
The answer is no if, additionally, we assume that there is an intensity for the total
treatment process $macron(N)$ in the filtration $cal(F)_t$ and, that,
for every other component there, likewise, exists an intensity,
and further that
$
    mean(Q_kappa) [Y_(t and S)] = mean(Q) [Y_(t and S)]
$
for every $cal(F)_t$-stopping time $S$.
*NOTE:* We can assume this to hold for slightly different exchangeability conditions
where we add $tilde(Y)_(dot and S)$ to the filtration at time zero.
Also simpler to just look at the filtrations with $tilde(Y)_(dot and event(k))$.
By the earlier constructions, we can actually get this independence statement. 

*NOTE:* We do not consider baseline elements. 
We will further assume that $cal(A) = {a_0, a_1}$ and that $pi^*_s (a_1) = 1$.
This can be proven in the following way.
First, note that $kappa$ only contains treatment martingales and by orthogonality
that the compensator in $Q_kappa$ of every other component than treatment will
be the same as in $P$. Likewise, assuming that $Q_kappa (tau^(g^*) = oo) = 1$,
we obtain that the compensator of $N^(a,a_0)$ in $Q_kappa$ must be zero.
That leaves the compensator $N^(a,a_1)$ in $Q_kappa$ to be specified. 
First take $S=event(1)$. Then, obtain that the corresponding component for
the compensator $N^(a,a_1)$ must be equal to that of $Q$ differentiating
and using properties of Lebesgue integrals. Continue in this manner for $S=event(2), event(3)$, etc.

*NOTE:* Can we make do with orthogonality?

= Comparison with Coarsening at Random (CAR) conditions of @onrobinsformula

NOTE: Need to add to explicitly add likelihood factorization to compare with the factorization of rytgaard.

Let us define the process by $Z (t) = (N^y (t), N^ell (t), L(t), N^a (t))$.
Consider also its potential outcome process $tilde(Z) = (tilde(N)^y, tilde(N)^ell, tilde(L), tilde(N)^a)$.
These are both multivariate cadlag processes.
Critically, we take $cal(F)_t = sigma(Z (s), s <= t)$
-- the natural filtration of the observed data process
and $cal(H)_t = cal(F)_t or sigma(tilde(Z) (dot))$.

Let $R$ denote the conditional distribution of $tau^(g^*)$ given $tilde(Z)$
(the conditional distributions exist since the sample space is Polish).
Before continuing, we discuss how this distribution is defined
and how it relates to our intervention.
First given the full process and hence the visitation times, the subject can only deviate
at the visitation times.
We now generate the process $A$. Let $A(0)=a_0$
and let $A(t) = a_0$ for $t < T_1$.
For each visitation time, i.e., $T_k$ with $Delta_k = a$, a new random variable
$A(T_k)$ is drawn based on the history up to that point, conditional on
$sigma(A(dot and T_(k-1)), tilde(Z))$.
Then, we put $A(t) = A(T_k)$ for $event(k) <= t < event(k+1)$.
Now let, $k^* := inf {k | status(k) = a, treat(k) != g^* (event(k), history(k-1))}$.
Then, $tau^(g^*) = event(k^*)$.
The coarsened data consists of $X=(tau^(g^*), tilde(Z)_(dot and tau^(g^*)))$.
For any finite $t>0$, this means that
$
    P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) &= sum_k P(event(k) in dif t, status(k) = a, treat(k) = 0, treat(k-1) = dots = treat(0) = 1 | tilde(Z) = tilde(z)) \
        &= sum_k P(treat(k) != g^* (event(k), history(k-1)) | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
        &quad times product_(j=1)^(k-1) (1- P(treat(j) = 0 | status(j) = a, treat(j-1) = dots = treat(0) = 1, tilde(Z) = tilde(z))) \
        &quad times P(event(k) in dif t, status(k) = a | treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
        &= sum_k P(treat(k) != g^* (event(k), history(k-1)) | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
        &quad times product_(j=1)^(k-1) (1- P(treat(j) = 0 | event(j), status(j) = a, treat(j-1) = dots = treat(0) = 1, tilde(Z) = tilde(z))) \
        &quad times bb(1) (tilde(t)_k in dif t, tilde(delta)_k = a). 
$ <eq:carseq>
(We allow the product to be empty, if the person dies before getting a visitation time).
Here, we use $tilde(t)_k$ and $tilde(delta)$ to denote the observed event times.
Let $k(tilde(z))$ denote the number of treatment event times in the observed sample.
Then, we also have that
$
    P(tau^(g^*) = oo | tilde(Z) = tilde(z)) = 1-sum_(j=1)^(k(tilde(z))) P(tau^(g^*) = t |  tilde(Z) = tilde(z))
$

In @onrobinsformula, it is assumed 
that
$
    P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) = p_(tau^(g^*)) (t | tilde(Z) = tilde(z)) mu (dif t),
$ <eq:car2>
for some $sigma$-finite measure $mu$ on $[0, oo]$.
(Note that we allow infinite values of $tau^(g^*)$,
corresponding to no treatment deviation).
They introduce a Coarsening at Random (CAR) condition
which in our setting can be stated as follows
$
    p_(tau^(g^*)) (t | tilde(Z) = tilde(z)) = h (t, tilde(z)_(dot and t))
$ <eq:car>
for some measurable function $h: [0, oo] times D_[0, oo) (RR^d) -> [0, 1]$,
where $D_[0, oo) (RR^d)$ denotes the space of càdlàg functions from $[0, oo)$ to $RR^d$.

Notably,
this choice of $mu$ may not depend on $tilde(z)$. This
is a problem as can be seen from the following proposition.

#theorem[
    Suppose that the treatment event times have discrete support,
    that is there is countable set $A$, including infinity, such that
    $P(event(k) in A, status(k) = a) = 1$.
    Then $mu$ can be taken to be the counting measure
    on $A$.
    Suppose that treatment event times are totally inacessible.
    Then, there exists no such $mu$.
]

#proof[
    The first statement is obvious. On the other hand, note that
    $nu := P(tau^(g^*) in dif t | tilde(Z))$ is a random measure. Its distribution is therefore determined
    by the Campbell measure $C_nu$.
    This means that for all measurable functions $h$ that
    $
        &mean(P) [integral h(s) nu (dif s)] \
            &=mean(P) [sum_(k) bb(1) {tilde(status(k)) = a} P(treat(k) != g^* (event(k), history(k-1)) | event(k), status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
                &times h(tilde(event(k)))] \
            &=mean(P) [integral h (s) p_(tau^(g^*)) (s | tilde(z)) mu (dif s)] \
            &=integral mean(P) [h (s) p_(tau^(g^*)) (s | tilde(z))] mu (dif s) \
    $
    Take $h(s) = bb(1) {tilde(status(k)) = a, tilde(event(k)) = s}$.
    By total inacesibility, we have that $mean(P) [h (s) p_(tau^(g^*)) (s | tilde(z))] = 0$.
    On the other hand, this is equal to
    $
        mean(P) [bb(1) {tilde(status(k)) = a} P(treat(k) != g^* (event(k), history(k-1)) | event(k), status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z))]
    $,
    which would imply that $bb(1) {tilde(status(k)) = a} P(treat(k) != g^* (event(k), history(k-1)) | event(k), status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z))$
    is almost surely equal to zero.
    This is generally almost equal to zero if there is probability > 0 for an event of type $a$ for the $k$'th event and
    2. non-degenerate treatment probabilities (the second is i.e., a positivity condition).
    We can ignore the first requirement suppose that there is a least one such $k$.
]

What @eq:carseq suggests is that we work with the following sequential condition:
$
    tilde(Z) perp bb(1) {treat(k) = g^*(event(k), history(k-1)) | event(k), status(k) = a, cal(F)^(g^*)_(event(k-1)),
$ <eq:sequentialcar>
so that @eq:carseq depends on observed data only.

One may try to relax @eq:car to the Markov kernel 
$
    P(tau^(g^*) = t | tilde(Z) = tilde(z)) = h (t, tilde(z)_(dot and t))
$
However, we are no longer guaranteed a result like Theorem 2.1
of @onrobinsformula or Theorem 25.40 of @vaart1998, without formally having to rederive it.
Let us just do this as it is not too difficult.

#theorem[
    Suppose that the distribution of $R$ is restricted by CAR and only CAR.
    Then $cal(P)^dot$ is dense in $L_2 (P)$.
]

#proof[
    Exactly the same as Theorem 25.40 in @vaart1998, but bound everything
    and consider specific submodels $Q^t = (1+t h) Q^0$, with $h$ bounded.
    First consider $R$,
    Submodels $R_t$ of $R$ are given by
    $
        sum_k bb(1) {status(k)=a} r_(t, k) (...) delta_(event(k))
    $
    Then,
    $
        integral sum_k ((((1+t h (x)) r_(t,k))^(1/2) - (r)^(1/2))/t - 1/2 (h (x) + a (y)) r)^2 P ... bb(1) {status(k) =a} delta_(event(k)) (dif t^a) dif Q^0 ->0
    $
    Add and subtract $(r_(t,k))^(1/2)/t$.
    NOTE: Subtle details about dominated convergence here?
    If we restricted to uniformly bounded "densities", then we would probably also get the result about every
    score being on a certain form. 
    Use also the argument to see that the scores for $R$ are functions of $X$ only...    
]

// Note: Let us consider whether or not the potential outcome process exists.
// Using orthogonality, use latent variables C_k and (T_k, Delta_k) to get observed data.
// Note: Need to make sure that, earlier, 

= Discussion

When applying data analysis in practical scenarios, a key question remains: how best to analyze 
the data at hand. We explore several potential interventions that could be relevant to those 
discussed in this article.
// For example, if using the same type of data, we could treat the first 
// deviation time as a censoring time, when a static intervention where the patient remains 
// on treatment at each visit is used. Incorporating the visitation times as a time-varying covariate would 
// likely yield an analysis similar to the one presented here.
// This would yield identification formulas that are identical to the one
// presented in @ryalenPotentialOutcomes, but for a potentially different target
// parameter, but would require that the total compensator such that the compensator has no discrete points.

Alternatively, a stochastic 
intervention could be considered, where both the timing of visits and the decisions surrounding 
them are intervened upon, so that the timing of visitation events is the same as in the observational data.
However, such interventions may be difficult to incorporate into a potential outcomes framework.
Finally, a simpler approach would be to entirely prevent patients from visiting the doctor, effectively eliminating any 
possibility of deviation from protocol.
//stoc int reflects ... scaling the intensity

In addition, a significant advantage of this approach, compared to 
preventative interventions, is the potential to model dynamic treatment regimes,
providing alternative means of analysis to the general ones in @ryalenPotentialOutcomes. 

#bibliography("references/ref.bib",style: "apa")


