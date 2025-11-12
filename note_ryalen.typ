#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.1": arkheion
#import "@preview/ctheorems:1.1.3": 
#set footnote(numbering: "*")

#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let example = thmbox("example", "Example", fill: rgb("#40FF40"))
#import "@preview/numty:0.0.5" as nt
#set cite(form: "prose")
// Color references red
#show  ref: it => {text(fill: maroon)[#it]}

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let proof = thmproof("proof", "Proof")
#let scr(it) = text(
  features: ("ss01",),
  box($cal(it)$),
)
#set math.equation(numbering: "(1)")
#show math.equation: it => {
  if it.block and not it.has("label") [
    #counter(math.equation).update(v => v - 1)
    #math.equation(it.body, block: true, numbering: none)#label("empty")
  ] else {
    it
  }  
}

#show: thmrules.with(qed-symbol: $square$)
#set heading(numbering: "1.a)")

#set cite(form: "prose")
#show ref: it => [#text(fill: blue)[#it]]
#show: arkheion.with(
    title: "Identification and Estimation of Causal Effects under Treatment-Assigned Interventions in Continuous Time",
    authors: (
        (name: "Johan S. Ohlendorff", email: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen", orcid: "0009-0006-8794-6641"),
        (name: "Pål Ryalen", email: "pal.ryalen@medisin.uio.no", affiliation: "University of Oslo", orcid: "0000-0002-3236-6782"),
        (name: "Kjetil Røysland", email: "kjetil.roysland@medisin.uio.no", affiliation: "University of Oslo", orcid: "0000-0001-5808-4903"),
        (name: "Anders Munch", email: "a.munch@sund.ku.dk", affiliation: "University of Copenhagen", orcid: "0000-0003-4625-1465"),
        (name: "Thomas A. Gerds", email: "tag@biostat.ku.dk", affiliation: "University of Copenhagen", orcid: "0000-0002-5955-816X"),
    ),
    abstract: [Marginal structural models (MSMs) provde a viable way to estimate longitudinal causal effects in discrete time.
        These require that the data are collected on a fixed time grid and thus may not provide inference for irregularly spaced observations.
        @rytgaardContinuoustimeTargetedMinimum2022 studied a marked point process, setting in which one intervenes on treatment assigned, but not
        the timing of treatment visits. In that article, no formal proof of the causal interpretation of the estimands was given.
        Also, no argument was given that the stated efficient influence function was the one under CAR and only CAR.
        We provide proof of these statements and compare with the recent work of @ryalenPotentialOutcomes. 
    ],
    keywords: ("causal inference", "continuous-time", "coarsening at random", "treatment-assigned interventions"),
)

#show math.equation: it => {
  if it.block and not it.has("label") [
    #counter(math.equation).update(v => v - 1)
    #math.equation(it.body, block: true, numbering: none)#label("empty")
  ] else {
    it
  }  
}

#show: thmrules.with(qed-symbol: $square$)

#show heading.where(level:1): it => {
  counter(math.equation).update(0)
  it
}

#set math.equation(numbering: n => {
  numbering("(1.1)", counter(heading).get().first(), n)
})

#set text(size: 10pt)
#show math.equation: set text(9pt)
#set image(width: 75%)

// In discrete time, the two formula are the same because every discrete time is a visitation event?
// What if we are still in discrete time, but the treatment decision is not made at every time point, but randomly; then it maybe does not relate to discrete time theories
// It appears then that the formulas can still be different. 

= Introduction

Robins' theory of causal inference for complex longitudinal data structures
provides a framework for causal inference
when treatments and covariates are measured at discrete time points (@robins1986).
Here, one wishes to identify the counterfactual mean outcome
under a specific treatment intervention. This has led
to the development of the g-formula,
which identifies the counterfactual mean outcome
under certain conditions via the observed data distribution
(@robins1986, @robins2000marginal, @RobinsLongitudinal2001).
These conditions require the assumptions of consistency,
sequential exchangeability, and positivity.
The exchangeability assumption is often dubbed "No unmeasured confounding";
however that term is somewhat misleading, as
there are actually multiple version of sequential exchangeability (@whatif).
However, many practical settings involve
continuous-time processes, where treatments and covariates may change at subject-specific times,
and thus causal inference at discrete time points may not appropriately
address time-varying confounding in such settings.
To address this, @lok2008 extended 
Robins' discrete-time framework to continuous time for nested structural models,
enabling the identification of causal effects in continuous-time settings
in terms of a counterfactual outcome process in survival analysis settings.
However, these models do place structural assumptions. 
It was then postulated in @gill2023causalinferencecomplexlongitudinal
how one may arrive at a continuous-time g-formula in general counting process settings,
extending the discrete-time g-formula of @RobinsLongitudinal2001
for marginal structural models to continuous time.
@rytgaardContinuoustimeTargetedMinimum2022
studied an intervention which does not change the timing of treatment visits,
but specifies treatment decisions at these visits
and provides a continuous-time g-formula without proof 
and corresponding estimation methods.
Recently, @ryalenPotentialOutcomes
developed a potential outcomes framework
for causal inference in continuous time,
establishing conditions for identifiability of the counterfactual mean outcome
under a continuous-time treatment intervention.
Although the two works appear similar,
the g-formulae defining their respective causal estimands generally differ.

We establish formal conditions under which the g-formula in @rytgaardContinuoustimeTargetedMinimum2022 identifies the counterfactual mean outcome under a continuous-time treatment intervention.
While that work introduced a g-formula and a sequential exchangeability condition, it did not provide a proof of identifiability.
Here, we present such a proof under slightly modified but intuitively related conditions and derive an equivalent martingale formulation.
Our approach fits naturally within the potential outcomes framework of @ryalenPotentialOutcomes.

It should be noted that any differences between the two arise only in exceptional, nonstandard settings;
in most practical cases, the identification formulae coincide.
Notably, our exchangeability condition admits a natural extension to a full exchangeability assumption,
which is equivalent to coarsening at random (CAR) -- an extension not available in @ryalenPotentialOutcomes.
We also provide an example illustrating that full exchangeability is strictly stronger than standard exchangeability.
(Finally, we extend Theorem 25.40 of @vaart1998 to show that only CAR implies a saturated model for the observed data distribution,
as the original theorem’s conditions are not directly applicable
in the continuous-time setting.)

== A (hypothetical) motivating application

Consider as an example a longitudinal study
in which a subject gets their measurements taken at baseline $L (0)$,
treatment assigned at baseline $A (0)$.
The patient is then followed throughout the interval $[0, T]$
at covariate visits and at treatment visits.
We let $N^a (t)$ and $N^ell (t)$ denote the number of treatment and covariate visits
before or at time $t$.
In our application, the covariates can only be measured 
the follow-up covariate visits; consisting of times $t in [0, T]$ at which $Delta N^ell (t) = 1$,
where they get their measurements taken. Similarly,
the follow-up visitation times decides exactly the times at which
treatment may change, that is at each time point $t$ with $Delta N^a (t) = 1$.
The outcome is typically taken as a measurable function of the history at time $t$, that is
$Y_t=sigma(L(dot and t), N^ell (dot and t))$.
Now consider as an example a randomized trial. The protocol states that at each doctors visit, the patient
should be treated. If the patient experiences adverse effects, the doctor may, in the real world, choose
to discontinue the treatment. We would like to know what would have happened if the patient
did indeed only receive treatment. The outcome we are then interested in saying something about is
$tilde(Y)_t$ representing the counterfactual world. So we are interested in estimating
$bb(E) [tilde(Y)_t]$; however, $tilde(Y)_t$ is typically not observed for all subjects.
Due to various issues with time-varying confounding (... Robins?), it is perhaps not obvious how to adjust for confounding.

=  Notation and setup

For an individual in a longitudinal causal inference study, it may be
of interest to assess what the causal effect of a treatment is.
We assume that all measurements are assumed to take place 
over a time interval $[0, T]$.
First, we let $N^y$ denote an outcome process $Y$ (e.g., death);
for each individual we also observe their treatment status $A$
and covariate process $L$ over time.
These processes are assumed to only change
whenever $N^x$ jumps for $x in {a, ell}$,
i.e., $Delta A (t) != 0$ only if $Delta N^a (t) = 1$
and $Delta L (t) != 0$ only if $Delta N^ell (t) = 1$.
We assume that these take on the values
$
    cal(A) &= {a_1, dots, a_k} \
    cal(L) &= {l_1, dots, l_m}.
$

At these times, the doctor may consider what treatment should be
assigned given the history of the individual up to that time.
The question that we wish to pose is 
what would have happened to the outcome process $N^y$
if at each visitation time, treatment decisions had been made
according to some treatment regime $g^*$, contrary to fact. 
For instance, this may be a regime
where treatment is always given or never given,
but could in principle also be a dynamic treatment regime
or random treatment regime.
These processes count the number of treatment and covariate events
for an individual.
It is implicitly assumed that $(N^y, N^a, N^ell)$
forms a multivariate counting process (@andersenStatisticalModelsBased1993).
Importantly, we also make the assumption of no explosion of $N$
which entails that  $P(N_T^y + N_T^a + N_T^ell < oo) = 1$.
In the first sections, we will be interested in identification and
thus not explicitly state anything about the statistical model $cal(M) = {P_theta : theta in Theta}$,
but only work with the true data-generating measure $P$.
Now we can let, for $n >= 1$
$
    T_((n)) = inf {t > T_((n-1)) : N_t^y + N_t^a + N_t^ell > n} "with" T_((0)) := 0.
$
These values are possibly infinite; then we can let
$
    Z_((n)) := (N^y (T_((n))), N^a (T_((n))), N^ell (T_((n))), A(T_((n))), L(T_((n)))).
$
Then, the marked point process given by $(T_((n)), Z_((n)))_(n >= 1)$ generates
the same natural filtration as $(N^y, N^a, N^ell, L, A)$ (Theorem 2.5.8 of @last1995marked).
Intuitively, this means that the information contained obtained from the multivariate
jump process is the same as that obtained from the marked point process at time $t$.
We can let $N^(a,a_j)$ be given by
$
    N^(a, a_j) (t) := sum_k bb(1) {T_((k)) <= t, A(T_((k))) = a_j}
$
Let $Lambda^(a, a_j) (t)$ denote the $P$-$cal(F)_t$-compensator of $N^(a, a_j)$
and $Lambda^a (t) = sum_(j=1)^k Lambda^(a, a_j) (t)$ denote the total $P$-$cal(F)_t$-compensator of $N^a$.
By the Radon-Nikodym theorem,
we can find kernels $pi_t (dif x)$
such that
$
    Lambda^(a, a_j) (dif t) = pi_t ({a_j}) Lambda^a (dif t).
$
or alternatively, we can work with the random measure
$
    N^a (dif t times dif x) := sum_(j=1)^k  delta_(A (t)) (dif x) N^(a) (dif t)
$
and its compensator
$
    Lambda^(a) (dif t times dif x) = pi_t (dif x) Lambda^a (dif t).
$

= Identification of the counterfactual mean outcome

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
What this means is that
$
    N^a ((0, t] times dif x) - Lambda^a ((0, t]) times dif x)
$
is a local $P$-$cal(F)_t$-martingale.
We shall write similar notations for the other components of $N$.
Let $scr(L)$ denote the $P$-$cal(F)_t$-canonical compensator of $N^(g^*)$.
However, $N^a$ generally has the compensator $Lambda^(a) (dif t times dif x) = pi_t (dif x) Lambda^a (dif t)$.
Now define the time to deviation from the treatment regime as
$
    tau^(g^*) = inf {t >= 0 | N^a ((0, t] times {x}) != N^(g^*) ((0, t] times {x}) " for some " x in cal(A)}.
$

#definition[
    Let $cal(tilde(F))_t := sigma(tilde(N)^y (dif s), tilde(N)^a (dif s times {x}), tilde(N)^ell (dif s times {y}) | s in (0, t], x in cal(A), y in cal(L))$.
    Let $Lambda$ denote the canonical $P$-$cal(F)_t$-compensator of $N$.

    A multivariate random measure $tilde(N) = (tilde(N)^y, tilde(N)^a, tilde(N)^ell)$
    is a *counterfactual random measure* under the intervention $g^*$
    if it satisfies the following conditions.
    1. $tilde(N)^a$ has compensator $scr(L) (tilde(N))$ with respect to $cal(tilde(F))_t$.
    2. $tilde(N)^x$, has the same compensator $Lambda (tilde(N))$ with respect to $cal(tilde(F))_t$ for $x in {y, ell}$.
]

Now let $(event(k))_k$ denote the ordered event times of $N$.
The main outcome of interest is the counterfactual outcome process
$tilde(Y) := tilde(N)^y$;
and we wish to identify $mean(P) [tilde(Y)_t]$.

//It has been discussed in discrete time (@RobinsLongitudinal2001)
//that the g-formula is unique; however, as we shall
//see the g-formula in continuous time may not necessarily be uniquely defined.
//Specifically this may relate to conditional distributions
//in this setting not being uniquely defined.
// We are interested in the counterfactual mean outcome $mean(P) [tilde(Y)_t]$,
// where $(tilde(Y)_t)_(t >= 0)$ is the counterfactual outcome process
// of $Y := N^y$ under the intervention that sets treatment to $1$ at all visitation times.
// Note the different exchangeability condition compared to @ryalenPotentialOutcomes,
// as @ryalenPotentialOutcomes expresses exchangeability through the counting process $bb(1) {tau^(g^*) <= dot}$.
//this appears to me to be a weaker condition (?).

Let $N^(a, x) (t) := N^a ((0, t] times {x})$ for $x in cal(A)$ and $M^(a, x) (t) := N^(a, x) (t) - Lambda^(a, x) (t)$.
Note that @eq:rytgaard is the same likelihood ratio as in @rytgaardContinuoustimeTargetedMinimum2022.
//We also assume that we work with a version of the compensator
//such that $Lambda ({t} times {y, a} times {1, 0}) < oo$ for all $t > 0$.
//We may generally also work with a compensator $Lambda$ that fulfills conditions (10.1.11)-(10.1.13) of @last1995marked.
// Let $pi_(event(k)) (history(k-1))$ denote the treatment probability
// and let $pi^*_(event(k)) (history(k-1))$ denote the treatment probability under the intervention $g^*$


// *NOTES:*
// - Does the exchangeability condition simplify in the case of $cal(n)^a$ predictable in $P$-$cal(F)_t$
//   as specified in @ryalenPotentialOutcomes; as noted in their article the two likelihood ratios
//   turn out two be the same in the case of orthogonal martingales.

//   Suppose that $cal(n)^a$ is predictable
//   so that $N^(a 1) (dif t)$ is predictable
//   in that case the first exchangeability condition is trivial;
//   Pål's condition only grants exchangeability for
//   $N^(a 1) (t and tau^(g^*)) $ is predictable;
//   I think that this is the sufficient for the argument to go through. 

// - Positivity holds for example if $pi_t$ is bounded away from $0$ and $1$
//   and $N_t$ has bounded number of jumps in the study period. 

// UI (Uniform integrability) implies zeta (t) = integral ... is uniformly integrable martingale,
// but why is integral_0^t tilde(Y)_(t) zeta (dif s) a martingale (generally a martingale)

// If there are two solutions (mine and theirs), they may be an infinite number of solutions
// due to convexity
//

// Would be nice to have some results about going back in forth between results on the compensator and the kernels in the canonical compensator
// Kjetil ment this would be possible. 

// Necessary criteria for the conclusion to hold
// for two measures Q in terms of P
// 1. E_P [tilde(Y)_t] = E_Q [Y_t]
// 2. Q(tau^(g^*) > t) = 1
// 3. Q and P are equivalent on cal(F)_t and the likelihood ratio is W(t)

// Look for restrictions on such that positivity in one situation implies the other
// It is natural to ask what the differences between the EIF in mine and Pål's paper are
// and whether the variance of one is smaller than the other?

// E_P[tilde(W)_t Y_t] = E_P[W_t Y_t]; can this hold? yes if E_P[tilde(W)_t | Y_t, W_t] = 1?
// Pål assumes that exchangeability holds for the weights; therefore E[tilde(Y)_t W_t] = E[tilde(Y)_t W_0]
// by conditioning.
// CAR is stronger than exchangeability => likelihood factorizes, but we do not need it to.
Note that alternatively, we can also require strong consistency.
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
    //line( (2,4.3), (2.7,4.3), mark: ( end: "o"), stroke: (paint: blue))
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


#theorem[
If _all_ of the following conditions hold:
- *Consistency*: $tilde(Y)_(dot) bb(1) {tau^(g^*) > dot} = Y_(dot) bb(1) {tau^(g^*) > dot} quad P-"a.s."$
- *Exchangeability*:
  Define $cal(H)_t := cal(F)_t or sigma(tilde(Y))$.
  // One version: Pål thinks they might be equivalent actually.
  //The $P$-$cal(H)_t$ Radon-Nikodym derivative of the compensator of $N^a$ with respect to the total $P$-$cal(H)_t$ compensator given by
  //$pi_t (dif x)$ is $cal(F)_t$-measurable.
  Let $Lambda^(a, a_j) (dif t) = pi_t ({a_j}) Lambda^(a) (dif t)$ denote the $P$-$cal(F)_t$-compensator of $N^(a, a_j)$ and $Lambda^(a,a_j)_H (dif t) = pi_t^H ({a_j}) Lambda^(a)_H (dif t)$ denote the $P$-$cal(H)_t$-compensator of $N^(a, a_j)$. $pi$ is indistinguishable from $pi^H$,
  that is for all $j in {1, dots, k}$ $P(pi_t ({a_j}) = pi_t^H ({a_j}), forall t in [0, T]) = 1$.

- *Positivity*: 
  $
      W (t) := product_(j = 1)^(N_t) (product_(i=1)^(k) ((pi^*_(event(j)) ({a_i}; history(j-1))) / (pi_(event(j)) ({a_i}; history(j-1))))^(bb(1) {treat(k) = a_i}))^(bb(1) {status(j) = a}) 
  $ <eq:rytgaard>
  is a uniformly integrable $P$-$cal(F)_t$-martingale.
  
  Furthermore, assume that $K(t) = integral_0^t sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s)$
  is a $P$-$cal(F)_t$-martingale and that $K$ is a process of *locally integrable variation*, meaning that $mean(P) [integral_0^t |d K(s)| ] < oo$ for all $t > 0$.

Then,
$
    mean(P) [tilde(Y)_t] = mean(P) [Y_t W (t)]
$
    and $W (t) = cal(E) (K)_t$ is a uniformly integrable $P$-$cal(F)_t$-martingale, where $cal(E)$ denotes the Doléans-Dade exponential (@protter2005stochastic).
] <thm:identifiabilitymartingale>

#proof[
    We shall use that the likelihood ratio solves a specific stochastic differential equation.
    To this end, note that
    $
        W(t) &= cal(E) (sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s))_t \
            &=^((*)) cal(E) (sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) - sum_(j=1)^(k) (pi_s^* ({a_j}) - pi_s ({a_j})) Lambda^(a) (dif s))_t \
            &= cal(E) (sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) - sum_(j=1)^(k) ((pi_s^* ({a_j})) / (pi_s ({a_j})) - 1) Lambda^(a, a_j) (dif s))_t \
            &= cal(E) (sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s))_t.
    $
    In $(*)$, we use that $sum_(j=1)^k pi_s ({a_j}) = sum_(j=1)^k pi_s^* ({a_j}) = 1$.
        
    Thus, by properties of the product integral (e.g., Theorem II.6.1 of @andersenStatisticalModelsBased1993),
    $
        W(t) = 1 + integral_0^t W(s -) sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s).
    $ <eq:sde>
    We have that
    $
        zeta_t := integral_0^t W(s -) sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) M^(a, a_j) (dif s)
    $ is a zero mean $P$-$cal(H)_t$-martingale by positivity.
    From this, we see that $integral_0^t tilde(Y)_(t) zeta (dif s)$ is also a uniformly integrable $P$-$cal(H)_t$-martingale
    by Theorem 2.1.42 of @last1995marked.
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

Note that in the proof, it suffices that $W(t)$ is uniformly bounded because
then it will also be a $P$-$cal(H)_t$-martingale
since it is a local, bounded $P$-$cal(H)_t$-martingale.

It is also natural to ask oneself: how does
our conditions
relate to the ones of @ryalenPotentialOutcomes?
The condition of consistency is the same.
However, the exchangeability condition and
the positivity condition are different in general.
We present slightly strengthened versions of the conditions
as these are easier to compare.
Let $bb(N)_t^a = bb(1) {tau^(g^*) <= t}$
and let $bb(L)_t$ denote its $P$-$cal(F)_t$-compensator.

- *Exchangeability*: 
  Define $cal(H)_t := cal(F)_t or sigma(tilde(Y))$.
  The $P$-$cal(F)_t$ compensator for $bb(N)^a$ is also the $P$-$cal(H)_t$ compensator.

- *Positivity*:
  $
      tilde(W) (t) := (cal(E) (-bb(N)^a))_t / (cal(E) (-bb(L)^a))_t = cal(E) (tilde(K))_t
  $
  is uniformly integrable, where $tilde(K)_t = integral_0^t 1/(1- Delta bb(L)^a_s ) (bb(N)^a (dif s) - bb(L)^a (dif s))$.
  Furthermore, $tilde(K)$ is a process of *locally integrable variation*
  and a $P$-$cal(F)_t$-martingale.

It is unclear at this point whether there exist potential outcomes processes
which fulfill the exchangeability condition and the consistency condition
for any observed data distribution of $N$.
We leave this question for future research.


= Full exchangeability vs standard exchangeability
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
        P(treat(1) = 0|event(1), status(1) = a, tilde(N)^y) = P(treat(1) = 0|event(1), status(1) = a),
    $
    but 
    $
        P(treat(1) = 0|event(1), status(1) = a, tilde(N)^y, tilde(N)^d) != P(treat(1) = 0|event(1), status(1) = a).
    $
    First note that if $event(1)$ and $tilde(T)_2$ have densities that
    $
        &P(treat(1) = 0|event(1) = t, status(1) = a, tilde(T)_2 = t_2, tilde(Delta)_2 = x, L=l) \
            &= (p_(event(1), status(1), tilde(T)_2, tilde(Delta)_2 | treat(1), L) (t, a, t_2, x | 0, l) P(treat(1) = 0 | L = l)) /(p_(event(1), status(1), tilde(T)_2, tilde(Delta)_2 | L) (t, a, t_2, x| l)) \
            &= (p_(tilde(T)_2, tilde(Delta)_2 | event(1), status(1), treat(1), L) (t_2, x | t, a, 0, l) p_(event(1), status(1)| treat(1), L) (t, a | 0, l) P(treat(1) = 0 | L = l)) /(p_(tilde(T)_2, tilde(Delta)_2 | event(1), status(1), L) (t_2, x| t, a,  l) p_(event(1), status(1) | L) (t, a | l)) \
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

= Comparison with @rytgaardContinuoustimeTargetedMinimum2022

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

//A lingering question is whether the desired $g$-formula
//can be obtained even if the martingales are not orthogonal.
#theorem("g-formula")[
    Let, further, $Q = W(T) dot P$ denote the probability measure defined by the likelihood ratio $W(T)$ given in @eq:rytgaard.
    //    Furthermore, let $Lambda_P^x$ denote the $P$-$cal(F)_t$-compensator of $N^x$ for $x in {y, ell}$.
    Under positivity, then
    1. The $Q$-$cal(F)_t$ compensator of $N^a (dif t times dif x)$ is $pi^*_t (dif x) Lambda_P^a (dif t)$.
    2. The $Q$-$cal(F)_t$ compensator of $N^x$ is $Lambda_P^x$ for $x in {y, ell}$. // addition should be zero; by Jacods formula for likelihood ratios
]

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
        chevron.l K, M^(a, x) chevron.r_t^P &= integral_0^t sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) dif chevron.l M_P^(a, a_j), M_P^(a, x) chevron.r_s^P \
            &= integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) dif chevron.l M_P^(a, x) chevron.r_s^P \
            &quad + sum_(j != x) integral_0^t ((pi_s^* (a_j))/(pi_s (a_j)) - 1) dif chevron.l M_P^(a, a_j), M_P^(a, x) chevron.r_s^P \
            &= integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) pi_s (x) Lambda_P^a (dif s) \
            &quad - integral_0^t ((pi_s^* (x))/(pi_s (x)) - 1) Delta (pi (x) Lambda_P^a)_s pi_s (x) Lambda_P^a (dif s) \
            &quad - sum_(j!= x) integral_0^t ((pi_s^* (a_j))/(pi_s (a_j)) - 1) Delta (pi (x) Lambda_P^a)_s pi_s (a_j) Lambda_P^a (dif s) \
            &= integral_0^t (pi_s^* (x) - pi_s (x)) Lambda_P^a (dif s) \
            &quad - sum_(j) integral_0^t (pi_s^* (a_j) - pi_s (a_j)) Delta (pi (x) Lambda_P^a)_s Lambda_P^a (dif s) \
            &= integral_0^t (pi_s^* (x) - pi_s (x)) Lambda_P^a (dif s).
    $ <eq:girsanova>
    Girsanov's theorem (Theorem 41, p. 136 of @protter2005stochastic)
    together with @eq:girsanov1 and @eq:girsanova
    gives that 
    $
        N^a (dif t times dif x) - pi_t (dif x) Lambda_P^a (dif t) - (pi_t^* (dif x) - pi_t (dif x)) Lambda_P^a (dif t) = N^a (dif t times dif x) - pi_t^* (dif x) Lambda_P^a (dif t)
    $
    is a $Q$-$cal(F)_t$-local martingale. The second statement follows by noting that
    $
        [M^(y), K]_t &= integral_0^t Delta N_t^y sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) N^(a, a_j) (dif s)  \
            &- integral_0^t Delta Lambda_P^y (s) sum_j ((pi_s^* (a_j))/(pi_s (a_j)) - 1) M^(a, a_j) (dif s) \
    $
    where we apply the trick with adding and subtracting the treatment compensators in the second term.
    The first term is zero because no two counting processes jump at the same time.
    The second term is a local martingale. This implies $chevron.l M^(y), K chevron.r_t^P = 0$.
    For $x=ell$ the argument is the same.
]

We now provide a sequential representation
of the exchangeability condition.
It aligns closely with the postulated exchangeability condition
in @rytgaardContinuoustimeTargetedMinimum2022;
however, notably on the conditioning set, we include
the $k$'th event time, which is not included in @rytgaardContinuoustimeTargetedMinimum2022.
We conclude that if we have independent marking for the treatment
process, the condition in @rytgaardContinuoustimeTargetedMinimum2022
is sufficient for causal identification. 

#theorem[
    Suppose consistency and positivity holds as in @thm:identifiabilitymartingale.
    Then, we have
    $
        mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t],
    $
    for all $t in [0, T]$, if for $k in bb(N)$
    and $t in [0, T]$ it holds that
    $
        tilde(Y)_t perp bb(1) {treat(k) = g^* (history(k-1), event(k))} | cal(F)^(g^*)_(event(k-1)), event(k) <= t, Delta N^a (event(k)) = 1,
    $
    where
    $
        cal(F)^(g^*)_event(k) = sigma(covariate(k), status(k), bb(1) {treat(k) = g_k^* (history(k-1), event(k))), dots, bb(1) {treat(0) = g_0^*(covariate(0))}, covariate(0))
    $
]
// should be able to do it witrh F_(T_k and t)
// look at conditions with both right censoring and coarsening

#proof[
    We see immediately that,
    $
        &integral W_(s-) bb(1) {event(m) < s < event(m+1) and t} dif K_s \
            &= W_(event(m)) integral bb(1) {event(m) < s < event(m+1) and t} dif K_s \
            &= W_(event(m)) bb(1) {event(m) < t} (sum_j (pi^*_(event(m)) ({a_j})) / (pi_(event(m)) ({a_j})) - 1) N^(a, a_j) (event(m+1) and t) \
//            &= W_(event(m)) bb(1) {event(m) < t} (product_j ((pi^*_(event(m)) ({a_j})) / (pi_(event(m)) ({a_j})))^(bb(1) {treat(k) = a_j}) - 1) N^(a, a_j) (event(m+1) and t) \
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
                &quad times mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) tilde(Y)_t | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1]] \
            &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                &quad times mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) | history(m), event(m+1) <=, Delta N^a (event(k)) = 1] \
                &quad times mean(P) [tilde(Y)_t | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1]] \
                        &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) \
                            &quad times mean(P) [mean(P) [((bb(1) {treat(m) = g_m^* (history(m), event(m+1))}) / (pi_(event(m)) ({g_m^* (history(m-1), event(m))}))- 1) | history(m), event(m+1), status(m+1)=a  | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1] \
                &quad times mean(P) [tilde(Y)_t | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1]] \
                    &= sum_(m=0)^(oo) mean(P) [W_(event(m)) bb(1) {event(m) < t} N^(a, a_j) (event(m+1) and t) times (1- 1) mean(P) [tilde(Y)_t | history(m), event(m+1) <= tau, Delta N^a (event(k)) = 1]] \
            &= 0.
    $
]

= On the existence of counterfactual processes fulfilling consistency and exchangeability

It is natural to ask oneself whether there exist counterfactual processes
for any given law of $N$ such that consistency and exchangeability holds,
that is can we extend the law of $N$ to some possibly larger sample space?
This question was already posed by @RobinsLongitudinal2001 in the discrete time setting.
If this does not hold, then, certainly, we would implicitly be imposing
restrictions on the observed data law of $N$. As the theorem below shows, it
is thus harmless to pretend that such counterfactual processes do in fact exist,
as they cannot be ruled out by the observed data law of $N$.

#theorem[
    For any law of $N$, we can construct a probability space,
    wherein a counterfactual process $tilde(N)$ and $N$ exists
    such that (strong) consistency and exchangeability holds.
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
    We also consider only the case where $cal(A) = {0, 1}$ and the static intervention $g^* (history(k-1), event(k)) = 1$ for all $k$.
    First, we let $(event(k), status(k), treat(k), covariate(k))_(k in NN)$ denote the marked point process
    corresponding to $N$ and $(treat(0), covariate(0))$ be the initial values of the treatment and covariate process.
    First, we generate $covariate(0)$ from its marginal distribution.
    Next, for $a_0 = 0, 1$, we generate $(L^(a_0)(T_((1))^(a_0)),T_((1))^(a_0), Delta^(a_0)_((1))) tilde covariate(1), event(1), status(1) | treat(0) = a_j, covariate(0)$
    (for each value of $a_0$, these can be generated independently).
    Next, for each $a_0 = 0, 1$ and each $a_1 = 0, 1$ where $Delta_((1))^(a_0) = a$, we generate
    $
        &(L^(a_0, a_1)(T_((2))^(a_0, a_1)), T_((2))^(a_0, a_1), Delta^(a_0, a_1)_((2))) \
            &tilde covariate(2), event(2), status(2) | covariate(1) = l_1, treat(1) = a_1, event(1) = t_1, status(1) = s_1, treat(0) = a_0, covariate(0)
    $
    where $(l_1, t_1, s_1) = (L^(a_0)(T_((1))^(a_0)),T_((1))^(a_0), Delta^(a_0)_((1)))$
    for $Delta^(a_0)_((1)) != y$ and $T^(a_0)_((1)) < T$. If $Delta^(a_0)_((1)) = y$, put $(L^(a_0, a_1)(T_((2))^(a_0, a_1)), T_((2))^(a_0, a_1), Delta^(a_0, a_1)_((2))) = (Ø, oo, Ø)$.
    Continue in this manner.
    Then, we define $tilde(N)$ by the marked point process
    $(L^(1, dots, 1)(T_((k))^(1, dots, 1)), 1, T_((k))^(1, dots, 1), Delta^(1, dots, 1)_((k)))_(k in NN)$
    with initial values in its filtration $(1, covariate(0))$.
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
    Continue in this manner.
    By construction, we then have
    $
        (tilde(N))_(t in [0, T]) perp treat(k) | history(k-1), event(k), status(k) = a
    $
    which suffices for exchangeability because it is stronger. Next, we show consistency.
    Define
    $
        tilde(Y)_t = sum_k bb(1) {T_((k))^(1, dots, 1) <= t, Delta^(1, dots, 1)_((k)) = y}
    $
    and
    $
        Y_t = sum_k bb(1) {event(k) <= t, status(k) = y}
    $
    Now note that
    $
        Y_t bb(1) {tau^(g^*) > t} &= sum_k bb(1) {event(k) <= t, status(k) = y} bb(1) {tau^(g^*) > t} \
            &= sum_k bb(1) {event(k) <= t, status(k) = y, treat(j) = 1, forall j < k} \
            &= sum_k bb(1) {T_((k))^(1, dots, 1) <= t, Delta^(1, dots, 1)_((k)) = y, treat(j) = 1, forall j < k} \
            &= sum_k bb(1) {T_((k))^(1, dots,1) <= t, Delta^(1, dots, 1)_((k)) = y} bb(1) {tau^(g^*) > t} \
            &= tilde(Y)_t bb(1) {tau^(g^*) > t},
    $
    as desired.
]

= Sequential criteria vs. martingale criteria

#theorem[
    Suppose that consistency holds
    and positivity holds, i.e., $W$ is uniformly integrable.
    Then,
    $
        (tilde(Y)_t)_(t in [0, T]) perp bb(1) {treat(k) = g^* (history(k-1), event(k))} | cal(F)^(g^*)_(event(k-1)), event(k), Delta N^a (event(k)) = 1,
    $
    for all $k in bb(N)$ if and only if $W(t)$ is $P$-$cal(F)_t$-measurable. 
]
#proof[
    Suppose that the sequential condition holds.
    Then, note that we can pick the Radon-Nikodym derivative for $cal(H)_t$ such that
    $
        pi_t ({a_j}) = sum_k bb(1) {event(k-1) < t <= event(k)} P(treat(k) = a_j | history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T]))
    $
    Therefore,
    $
        (pi^*_t ({a_j})) / (pi_t ({a_j})) = sum_k bb(1) {event(k-1) < t <= event(k)} (bb(1) {g^* (history(k-1), event(k)) = a_j}) / P(treat(k) = a_j | history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T]))
    $
    Noting that also $W (t) = W (t) bb(1) {tau^(g^*) > t}$.
    Therefore, each of the terms in the product expansion of $W(t)$
    can really be written in terms
    of $cal(F)^(g^*)_(event(k-1))$ instead of $history(k-1)$, i.e., in $W(t)$, we have
    $
        (pi^*_t ({a_j})) / (pi_t ({a_j})) = sum_k bb(1) {event(k-1) < t <= event(k)} (bb(1) {g^* (history(k-1), event(k)) = a_j}) / P(treat(k) = a_j | cal(F)^(g^*)_(event(k-1)), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T]))
    $
    However, by the sequential condition,
    this is also
    $
        (pi^*_t ({a_j})) / (pi_t ({a_j})) = sum_k bb(1) {event(k-1) < t <= event(k)} (bb(1) {g^* (history(k-1), event(k)) = a_j}) / P(treat(k) = a_j | cal(F)^(g^*)_(event(k-1)), event(k), status(k) = a)
    $
    which makes $W(t)$ $cal(F)_t$-measurable.
    Conversely, suppose that $W(t)$ is $cal(F)_t$-measurable.
    Then, we have $W(event(k)) / W(event(k-1)) bb(1) {tau^(g^*) > event(k-1), event(k-1) < oo}$ is $cal(F)_(event(k))$-measurable.
    However, this is equal to $((bb(1) {treat(k) = g^* (history(k-1), event(k))})
    /(P(treat(k) = g^* (history(k-1), event(k)) | history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T]))))^(bb(1) {status(k+1) = a} $
    is $cal(F)_(event(k))$-measurable.
    Conclude that
    $
        bb(1) {treat(k) = g^* (history(k-1), event(k)), status(k) = a} 1/P(treat(k) = g^* (history(k-1), event(k)) | history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T]))
    $
    is $cal(F)_(event(k))$-measurable.
    This means that there is a measurable function $f$ such that
    $
        &bb(1) {treat(k) = g^* (history(k-1), event(k)), status(k) = a} 1/P(treat(k) = g^* (history(k-1), event(k)) | history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T]))\
            &= f(event(k), status(k), treat(k), covariate(k), dots, treat(0), covariate(0)) \
            &= bb(1) {treat(k) = g^* (history(k-1), event(k)), status(k) = a} f (event(k), status(k), treat(k), covariate(k), dots, treat(0), covariate(0)) \
            &=bb(1) {treat(k) = g^* (history(k-1), event(k)), status(k) = a} f (event(k), a, g^* (history(k-1), event(k)), covariate(k), dots, treat(0), covariate(0)) \
    $
    Take the conditional expectation on both sides to conclude that
    $
        P(treat(k) = g^* (history(k-1), event(k)) | history(k-1), event(k), status(k) = a, (tilde(Y)_t)_(t in [0, T]))
    $
    is $cal(F)_(event(k))$-measurable whenever the probability is non-zero.
    This suffices for the sequential condition.
    //Note: Are versions adapted here? Yes because the kernel must be equal to the probabilities at the stopping times 
]

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

Note that if one exchangeability in terms of @thm:identifiabilitymartingale holds,
then both identification formulas are the same i.e.,
$
    mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t] = mean(P) [tilde(W)_t Y_t],
$

#theorem[
    Consider the static intervention with $g^* (history(k-1), event(k)) = 1$ for all $k$.
    and $cal(A) = {0, 1}$.
    Suppose consistency for $tilde(Y)_t$ as in @thm:identifiabilitymartingale.
    Let $pi^cal(H)_t (1)$, $pi^cal(F)_t (1)$
    denote the Radon-Nikodym derivatives of $Lambda^(a, 1)$
    with respect to $Lambda^(a)$
    in the filtrations $cal(H)_t$ and $cal(F)_t$, respectively.
    Similarly, let $Lambda^(a, cal(H))$, $Lambda^(a, cal(F))$
    denote the compensators of $N^a$ in the filtrations $cal(H)_t$
    and $cal(F)_t$, respectively.
    Suppose that a version of $pi_s^cal(F))$ exists such that
    $
        pi_s^cal(F) (1, omega) < 1
    $ <eq:nonperfectcompliance>
    for all $s in [0, T]$ and $omega in Omega^*$ with $P(Omega^*) = 1$.
    Also, suppose that strong consistency holds for $tilde(N)_t^a$, i.e.,
    $
        tilde(N)_dot^a bb(1) {tau^(g^*) >= dot} = N_dot^a bb(1) {tau^(g^*) >= dot} quad P-"a.s."
    $
    Let $cal(H)_t$ denote the initial expansion of
    $cal(F)_t$ with $sigma(tilde(N)_dot^a, tilde(Y)_dot)$.
    If the compensator of $bb(N)^a$ in the filtration $cal(H)_t$ is 
    $cal(F)_t$-predictable, then $N^a (dot and tau^(g^*))$
    is $cal(F)_t$-predictable. 
]
#proof[

// Then, we have that
// $
//     mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t]
// $
// by @thm:identifiabilitymartingale if $W_dot$ is a uniformly integrable martingale.

// However, note that
// $
//     bb(L)_t^a &= integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a) (dif s) \
//         &= integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s).
// $ <eq_bbL>
// is a $cal(H)_t$-compensator of $bb(N)^a$.
// Here, we use that the compensator of $bb(1) {bb(N)_(s-)^a = 0} N^a (dif s)$
// is $bb(1) {bb(N)_(s-)^a = 0} N^a (dif s)$ itself in the filtration $cal(H)_t$.
// If $tilde(W)_t = cal(E) (-bb(K)^a)_t$ is such that it is a $P$-$cal(H)_t$-martingale (integrability conditions),
// then it will be a $P$-$cal(F)_t$-martingale as well,
// where $bb(K)^a_t = integral_0^t 1/(1 - Delta bb(L)_s^a) dif bb(M)_s^a$,
// by the stated argument since the compensator of $bb(N)^a$ in $cal(H)_t$
// is also $cal(F)_t$-adapted.
// Nonetheless, @eq_bbL in itself almost never be $cal(F)_t$-predictable,
// leading to possible issues -- also about the existence of such a $bb(L)^a$
// if treatment compensator is continuous in $cal(F)_t$, then it will almost never be able to the above?
// Conclude that if this is the case, then exchangeability in Påls setting can never hold.

Note that, under the stated conditions
$
        integral_0^dot bb(1) {s <= tau^(g^*)} N^(a) (dif s)
$
is a $cal(H)_t$-predictable process.
Therefore, it is its own compensator in $cal(H)_t$.
Now note that
$
    bb(L)^cal(H)_dot &= integral_0^dot  (1-pi^(cal(H))_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(H)) (dif s) \
        &= integral_0^dot  (1-pi^(cal(H))_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s).
$
On the other hand,
$
    bb(L)_dot^cal(F) &= integral_0^dot  (1-pi^(cal(F))_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(F)) (dif s) 
$
Conclude that if $bb(L)^cal(H)$ is indistinguishable from $bb(L)^cal(F)$,
then
$
    (1-pi^(cal(H))_dot (1)) bb(1) {dot <= tau^(g^*)} Delta N^a (dot) = (1-pi^(cal(F))_dot (1)) bb(1) {dot <= tau^(g^*)} Delta Lambda^(a,cal(F)) (dot).
$
Therefore,
$
    bb(L)^cal(H)_dot = integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
$
on a set up to $P$-indistinguishability.
If this were $cal(F)_t$-predictable, then
$
    bb(L)^cal(H)_dot &= integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
        &= integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} M^(a, cal(F)) (dif s) + integral_0^t  (1-pi^(cal(F))_s (1)) Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(F)) (dif s) 
$
Conclude that since
$integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} M^(a, cal(F)) (dif s)$
is a difference of two non-decreasing processes, and hence of finite variation,
a local martingale,
by p. 115 of @protter2005stochastic that 
$
    integral_0^dot (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} N^(a) (dif s) = integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} Lambda^(a, cal(F)) (dif s).
$
Then, we have that $bb(1) {dot <= tau^(g^*)} Delta Lambda^(a,cal(F)) (T^a_(k)) = -1$ by @eq:nonperfectcompliance
for all jump times $T_(k)^a$ of $N^a$.
However, we also have that
$
    bb(1) {s <= tau^(g^*)} Delta Lambda^(a,cal(F)) (s) = 0
$
whenever $s$ is not a jump time of $N^a$ by @eq:nonperfectcompliance.
This shows the statement for the discrete part of the compensator.
For the continuous part, we are now able to conclude from these two parts that
$
    integral_0^dot  (1-pi^(cal(F))_s (1))  Delta Lambda^(a,cal(F)) (s) bb(1) {s <= tau^(g^*)} lambda^(a, cal(F)) (s) dif s = 0
$
from which we conclude that
$
        bb(1) {s <= tau^(g^*)} lambda^(a, cal(F)) (s) = 0
$
for almost all $s$ with respect to the Lebesgue measure
    and almost all $omega in Omega^(**)$ with $P(Omega^(**)) = 1$.
However, these two restrictions exactly mean that $bb(1) {s <= tau^(g^*)} N^a (dif s)$
is a $cal(F)_t$-predictable process.
]

This is because
$
    bb(L)_t^a = integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} M^(a) (dif s) + integral_0^t  (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Lambda^(a) (dif s).
$
which implies under regularity conditions that $bb(1) {s <= tau^(g^*)} N^a (dif s)$
is a predictable process in $cal(F)_t$.
Now, we calculate
$
    bb(K)_t^a &= -integral_0^t 1/(1 - Delta bb(L)_s^a) dif bb(M)_s^a \
        &= -integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(M)_s^a \
        &= -integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(N)_s^a \
        &+ integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(L)_s^a \
        &=- integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(N)_s^a \
        &+ integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) (1-pi_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
        &=- integral_0^t 1/(1- (1-pi_s (1)) bb(1) {s <= tau^(g^*)} Delta N^a (s)) dif bb(N)_s^a \
        &+ integral_0^t 1/(pi_s (1)) (1-pi_s (1)) bb(1) {s <= tau^(g^*)} N^(a) (dif s) \
        &= K_t^*
$

On the other hand, the same argument shows that if the other exchangeability condition holds
then $pi_s (1) bb(1) {s <= tau^(g^*)}$ can be chosen $cal(F)_t$-adapted,
since we can pick
$
    pi_s (1) = sum_k bb(1) {event(k-1) < s <= event(k)} (1- Delta bb(L)_(event(k-1))^a) //(0 bb(1) {status(k-1) = a, event(k-1) > tau^(g^*)} + (1- Delta bb(L)_(event(k-1))^a) bb(1) {status(k-1) = a, event(k-1) <= tau^(g^*)}).
$
By construction, $pi_s (1)$ is the desired Radon-Nikodym derivative with respect to $cal(H)_t$.
Moreover, it is $cal(F)_t$-adapted since $Delta bb(L)_(event(k-1))^a$ is $cal(F)_(event(k-1))$-measurable.x
Therefore, again, the weight $W(t)$ is a $P$-$cal(H)_t$-martingale as well
and $cal(F)_t$-adapted under integrability conditions.
Therefore, we have that
$
    mean(P) [tilde(Y)_t] = mean(P) [W_t Y_t]
$
also. Now calculate
$
    K_t^* &= integral_0^t bb(1) {s <= tau^(g^*)} (1/(pi_s (1)) - 1) N^(a,1) (dif s) + integral_0^t bb(1) {s <= tau^(g^*)} ( - 1) N^(a,0) (dif s) \
        &= integral_0^t bb(1) {s <= tau^(g^*)} sum_k bb(1) {event(k-1) < s <= event(k)} (1/(pi_s (1)) - 1) N^(a,1) (dif s) + integral_0^t bb(1) {s <= tau^(g^*)} ( - 1) N^(a,0) (dif s) \
        &= sum_k integral_(event(k-1) and t)^(event(k) and t) bb(1) {s <= tau^(g^*)} (1/(1-Delta bb(L)_(event(k-1))^a ) - 1) N^(a,1) (dif s) + integral_0^t bb(1) {s <= tau^(g^*)} ( - 1) N^(a,0) (dif s) \
        &=  sum_k integral_(event(k-1) and t)^(event(k) and t) bb(1) {s <= tau^(g^*)} (Delta bb(L)_(event(k-1))^a)/(1-Delta bb(L)_(event(k-1))^a ) N^(a,1) (dif s) + integral_0^t bb(1) {s <= tau^(g^*)} ( - 1) N^(a,0) (dif s) \
        &= bb(K)_t^a.
$

// #theorem[
// CAR holds if and only if for each $k in bb(N)$
//     $
//         tilde(Z) perp treat(k) | event(k), status(k) = a, cal(F)_(event(k-1))^(a=1),
//     $
//     where $cal(F)_t^(a=1) = sigma((N^y (s), N^ell (s), L(s), N^a (s), 1), s <= t)$.
// ]
// Note that 
// $
//     P(tau^(g^*) <= t | tilde(Z) = tilde(z)) = sum_k P(event(k) <= t, status(k) = a, treat(k) = 0, treat(k-1) = dots = treat(0) = 1 | tilde(Z) = tilde(z))
// $
// as a consequence, we have
// $
//     P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) &= sum_k P(event(k) in dif t, status(k) = a, treat(k) = 0, treat(k-1) = dots = treat(0) = 1 | tilde(Z) = tilde(z)) \
//         &= sum_k P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &quad times P(event(k) in dif t, status(k) = a | treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &= sum_k P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &quad times bb(1) (t_k in dif t, delta_k = a). 
// $ <eq:carseq>
// This is because given everything else $event(k) in dif t, status(k) = a$ is a measurable function of $tilde(Z)$
// if deviation has not occured yet. 
// Since, under the assumption, we have that,
// $
//     &P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &= P(treat(k) = 0 | event(k) = t, status(k) = a, cal(F)_(event(k-1))^(a=1) = f_(t_(k-1))^(a=1)) \
// $
// then CAR holds using consistency.

// Conversely assume that CAR holds.
// From @eq:carseq, we have that
// $
//     &bb(1) {t_(k-1) < t <= t_k} P(tau^(g^*) in dif t | tilde(Z) = tilde(z)) \
//         &= P(treat(k) = 0 | event(k) = t, status(k) = a, treat(k-1) = dots = treat(0) = 1, tilde(Z) = tilde(z)) \
//         &times bb(1) {t_(k-1) < t <= t_k} bb(1) {t_k in dif t, delta_k = a}.
// $
// , where $cal(F)_(event(k-1))^(- "a")$ is the stopping time $sigma$-algebra
// for the natural filtration without the treatment process $A(t)$.
// For this one, it suffices
// that
// $
//     treat(k) perp tilde(Z) | event(k), status(k) = a, treat(k-1) = dots = treat(0) = 1, cal(F)_(event(k-1))^("a" = 1)
// $
// for each $k$, which is what we were working with $tilde(Y)$ instead of $tilde(Z)$.
// However, the only thing I needed to use was that $bb(1) {event(k) <= t, status(k) = a}$ is a measurable function of $tilde(Z)$
// of $treat(k-1) = dots = treat(0) = 1$.
// Maybe these two are equivalent?




// For given laws of $N$ with a perfect compliance at baseline,

// Consider the simple mark point process $(event(2), treat(1), status(1), event(1), covariate(0))$.
// We show that there exist settings in which CAR does not hold,
// but the exchangeability condition of @thm:identifiabilitymartingale does hold.
// We may generate a potential outcome process $tilde(N)$
// as in the proof of @thm:existencecounterfactuals
// with baseline covariate $covariate(0)$. We show that our exchangeability condition holds for the filtration
// that does not include $covariate(0)$, but CAR does not hold.
// We choose $P(treat(1) = 1 | event(1), status(1) = a, treat(0) = 0, covariate(0) = 0) = 1/2$
// which by our construction will also mean that $P(treat(1) = 1 | event(1), status(1) = a, treat(0) = 0, covariate(0) = 1, tilde(N) = tilde(n)) = 1/2$.
// Need to also construct it such that
// $
//     &g^0 (t) = P (event(1) <= t, status(1) = a | tilde(T)_2 = t_2, covariate(0) = 0) = P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0) = 0) \
//         &!= P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0) = 1) = P (event(1) <= t, status(1) = a | tilde(T)_2 = t_2, covariate(0) = 1) = g^1 (t)
// $
// for example if the distribution of $event(2)$ depends only on $covariate(0), status(k) = a$ and only on $event(1)$ through the relation $event(2) > event(1)$,
// this will hold I think. Explicitly find this distribution with Bayes formula probably.
// Then,
// $
//     P (tau^(g^*) <= t | tilde(N) = tilde(n) ) &= P (event(1) <= t, status(1) = a, treat(1) = 0 | tilde(N) = tilde(n) ) \
//         &= mean(P) [P (event(1) <= t, status(1) = a, treat(1) = 0 | tilde(N) = tilde(n), covariate(0))| tilde(N) = tilde(n)] \
//         &= mean(P) [P(treat(1) = 0 | event(1) <= t, status(1) = a, tilde(N) = tilde(n), covariate(0)) \
//             &times P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0)) | tilde(N) = tilde(n)] \
//         &= mean(P) [1/2 P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0)) | tilde(N) = tilde(n)] \
//         &= 1/2 P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0) = 0) P(covariate(0) = 0 | tilde(N) = tilde(n)) \
//         &+ 1/2 P (event(1) <= t, status(1) = a | tilde(N) = tilde(n), covariate(0) = 1) (1-P(covariate(0) = 0 | tilde(N) = tilde(n))) \
    
// $
// This shows the desired statement ... just need to come up with some distributions. 
// In the next example construct it such that
// $
//     P (event(1) <= t, status(1) = a, treat(1) = 0 | tilde(N) = tilde(n)) = h (t)
// $
// while
// $
//     P (event(1) <= t, status(1) = a, treat(1) = 1 | tilde(N) = tilde(n), covariate(0)) != h (t)
// $

= Comparison between @ryalenPotentialOutcomes and @rytgaardContinuoustimeTargetedMinimum2022

Consider a simple example where $N^a (t) <= 1$ for all $t$,
and consists of the multivariate counting process $N = (N^y, N^(a,a_0), N^(a,a_1))$.
We consider the intervention $pi^*_t (a_1) = 1$ for all $t$.
Suppose that $(N^y, N^(a,a_0), N^(a,a_1))$ has compensator
$
    Lambda^y (dif t) (P) &= lambda_t^y dif t, \
    Lambda^(a,a_j) (dif t) (P) &= pi_t (a_j) lambda_t^a dif t, j=0,1.
$
with respect to $cal(F)_t$ in $P$.
In $P$, note that
$
    mean(P) [Y_t] &= mean(P) [N^y (t)] \
        &= mean(P) [bb(1) {event(1) <= t, status(1) = y} \
            &+ bb(1) {status(1) = a, treat(1) = 1, event(2) <= t, status(2) = y}\
            &+ bb(1) {status(1) = a, treat(1) = 0, event(2) <= t, status(2) = y}]\
        &= integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a,a_1) + lambda_u^(a,a_0)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a,a_1) + lambda_u^(a,a_0)) dif u) lambda_s^(a,a_1) \
        &quad times integral_s^t exp(- integral_s^v lambda_u^y ) dif u) lambda_v^y dif v dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a,a_1) + lambda_u^(a,a_0)) dif u) lambda_s^(a,a_0) \
        &quad times integral_s^t exp(- integral_s^v lambda_u^y ) dif u) lambda_v^y dif v dif s \
$

Then, in $Q$, we have
$
    Lambda^y (dif t) (Q) &= lambda_t^y dif t, \
    Lambda^(a,a_0) (dif t) (Q) &= 0, \
    Lambda^(a,a_1) (dif t) (Q) &= lambda_t^a dif t.
$
Therefore,
$
    mean(Q) [Y_t] &= mean(Q) [N^y (t)] \
        &= mean(Q) [bb(1) {event(1) <= t, status(1) = y} \
            &+ bb(1) {status(1) = a, treat(1) = 1, event(2) <= t, status(2) = y}]\
        &= integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
        &= integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a) \
        &quad times (1-exp(- integral_s^t lambda_u^y dif u)) dif s \
        &= 1- exp(- integral_0^t (lambda_u^y + lambda_u^(a)) dif u) - integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^a dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a) \
        &quad times (1-exp(- integral_s^t lambda_u^y dif u)) dif s \
        &= 1- exp(- integral_0^t (lambda_u^y + lambda_u^(a)) dif u) \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a) exp(- integral_s^t lambda_u^y dif u) dif s \
        &=^(!) 1- exp(- integral_0^t (lambda_u^y + lambda_u^(a)) dif u) \
        &- exp(-integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (lambda_u^(a)) dif u) lambda_s^(a) dif s \
        &= 1- exp(- integral_0^t (lambda_u^y + lambda_u^(a)) dif u) \
        &- exp(-integral_0^t lambda_u^y dif u) (1-exp(- integral_0^t (lambda_u^(a)) dif u)) \
        &= 1 - exp(- integral_0^t lambda_u^y dif u)
$
In (!) use that $lambda^y (u)$ does not depend on $s$ at all (jump time $a$).
With constant intensities and constant treatment probabilities, this reduces to
$
    mean(Q) [Y_t] &= integral_0^t exp(- (lambda^y + lambda^(a)) s) lambda^y dif s \
        &+ integral_0^t exp(- (lambda^y + lambda^(a)) s) lambda^(a) \
        &quad times (1-exp(- lambda^y (t-s))) dif s \
        &= (lambda^y /(lambda^y + lambda^(a))) (1-exp(- (lambda^y + lambda^(a)) t)) \
        &+ (lambda^(a)/(lambda^y + lambda^(a))) (1-exp(- (lambda^y + lambda^(a)) t)) - lambda^(a) exp(- lambda^y t)/(lambda^a) (1-exp(- lambda^a t)) \
        &= (1-exp(- (lambda^y + lambda^(a)) t)) - exp(- lambda^y t)(1-exp(- lambda^a t)) \
        &= 1 - exp(- lambda^y t) 
$
Now consider "a going to the Tivoli example" in which
the visit itself directly affects the probability of dying.
$
    mean(Q) [Y_t] &= integral_0^t exp(- (lambda^y + lambda^(a)) s) lambda^y dif s \
        &+ integral_0^t exp(- (lambda^y + lambda^(a)) s) lambda^(a) \
        &quad times (1-exp(- lambda^(y,2) (t-s))) dif s \
        &= (lambda^y /(lambda^y + lambda^(a))) (1-exp(- (lambda^y + lambda^(a)) t)) \
        &+ (lambda^(a)/(lambda^y + lambda^(a))) (1-exp(- (lambda^y + lambda^(a)) t)) - lambda^(a) exp(- lambda^(y,2) t)/(lambda^a+lambda^y+lambda^(y,2)) (1-exp(- (lambda^a + lambda^y+lambda^(y,2)) t)) \
        &= 1-exp(- (lambda^y + lambda^(a)) t) - lambda^(a) exp(- lambda^(y,2) t)/(lambda^a+lambda^y-lambda^(y,2)) (1-exp(- (lambda^a + lambda^y-lambda^(y,2)) t))
$

However, in $tilde(Q)$ (Ryalen), we have
$
    Lambda^y (dif t) (tilde(Q)) &= (lambda_t^y dif t-0)/(1-0), \
    Lambda^(a,a_0) (dif t) (tilde(Q)) &= (0-0)/(1-0) \
    Lambda^(a,a_1) (dif t) (tilde(Q)) &= (lambda_t^a dif t - (1-pi_(t and tau^(g^*))(a_1)) lambda^a_(t and tau^(g^*)) dif t)/(1-0) = pi_(t and tau^(g^*))(a_1) lambda^a_(t and tau^(g^*)) dif t = pi_(t)(a_1) lambda^a_(t) dif t.
$
since $tau^(g^*) = oo$ almost surely in $tilde(Q)$.
With constant intensities, we get the same as above plugging in $pi lambda^a$ instead of $lambda^a$.
Therefore,
$
    mean(tilde(Q)) [Y_t] &= mean(tilde(Q)) [N^y (t)] \
        &= mean(tilde(Q)) [bb(1) {event(1) <= t, status(1) = y} \
            &+ bb(1) {status(1) = a, treat(1) = 1, event(2) <= t, status(2) = y}]\
        &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
        &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times (1-exp(- integral_s^t lambda_u^y dif u))  dif s \ 
$
We now consider a more natural example, where the difference is due to time-varying confounding.
Påls functional can be written as
$
    &integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) (lambda_v^y + lambda^ell_v integral_v^t exp(- integral_v^w lambda_u^y (ell_2; v) dif u) lambda^y_w (ell_2; v) dif w) dif v dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u) \
        &quad times (lambda_v^y (ell_1 ; s) + pi_v (a_1) (ell_1 ; s) lambda_v^(a) (ell_1 ; s) integral_v^t exp(- integral_v^w lambda_u^y (ell_1 ; s) dif u) lambda^y_w (ell_1; s) dif w) dif v dif s \
        &=integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) lambda_s^y dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) (lambda_v^y + lambda^ell_v (1- exp(- integral_v^t lambda_u^y (ell_2; v) dif u))) dif v dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u) \
        &quad times (lambda_v^y (ell_1 ; s) + pi_v (a_1) (ell_1 ; s) lambda_v^(a) (ell_1 ; s) (1-exp(- integral_v^t lambda_u^y (ell_1 ; s) dif u)) dif v dif s \
$
Can we conclude this result does not depend on $pi_t (a_1)$?
Now, note that
$
    &integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) lambda_s^y dif s \
        &=[- exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u)]_0^t - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) (pi_s (a_1) lambda_s^(a) + lambda_s^ell) dif s \
        &= 1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) (pi_s (a_1) lambda_s^(a) + lambda_s^ell) dif s \    
$
Conclude that the previous is equal to
$
    &1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) dif s \
        &-integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(- integral_s^t (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))) dif s \
    &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u) \
        &quad times pi_v (a_1) (ell_1 ; s) lambda_v^(a) (ell_1 ; s) exp(- integral_v^t lambda_u^y (ell_1 ; s) dif u) dif v dif s \
    &=1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) dif s \
        &-integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(- integral_s^t (lambda_u^y (ell_1; s) + pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))) dif s \
    &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell \
        &quad times exp(-integral_s^t lambda_u^y (ell_1; s) dif u) (1-exp(- integral_s^t (pi_u (a_1) (ell_1; s) lambda_u^a (ell_1 ; s))  dif u)) dif s \
$
$
        &1 - exp(- integral_0^t (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell ) dif u) \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) dif s \
    &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
            &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y (ell_1; s) dif u) dif s \
    &=1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
    &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
        &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
        &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y (ell_1; s) dif u) dif s 
$
We now apply integration by parts to the last two terms.
Let $h(v, s) = exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u)$.

Obtain
$
    &integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) integral_s^t h(v,s) dif v dif s \
        &=[- exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v]^(s=t)_(s=0) \
        &- integral_0^t (- exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) (partial)/(partial s) integral_s^t h(v,s) dif v) dif s \
        &- integral_0^t ((lambda_s^y + lambda_s^ell) exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v) dif s \
        &= integral_0^t h(v,s) dif v + integral_0^t (exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) (partial)/(partial s) integral_s^t h(v,s) dif v) dif s \
        &- integral_0^t ((lambda_s^y + lambda_s^ell) exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v) dif s \
                &= integral_0^t h(v,s) dif v - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) h(s,s) dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t (partial)/(partial s) h(v,s) dif v dif s \
        &- integral_0^t ((lambda_s^y + lambda_s^ell) exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v) dif s \
        &= integral_0^t h(v,s) dif v - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda^ell_v exp(- integral_s^t lambda_u^y (ell_2; s) dif u) dif s \
        &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t (partial)/(partial s) h(v,s) dif v dif s \
        &- integral_0^t ((lambda_s^y + lambda_s^ell) exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) integral_s^t h(v,s) dif v) dif s \
        &= integral_0^t h(v,s) dif v - integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda^ell_v exp(- integral_s^t lambda_u^y (ell_2; s) dif u) dif s \
$
Since it is assumed that $lambda_u^y (ell_2; s) = lambda_u^y (ell_1; s)$,
we finally have that
$
    1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) - integral_0^t h(v,s) dif v
$
which does not depend on $pi_t (a_1)$.
These conclusions should generalize and work under an orthogonal martingales assumption. 
// $
//     &1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//     &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y (ell_2; v) dif u) dif v dif s \
//         &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y (ell_1; s) dif u) dif s \
//         &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//     &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u) lambda^ell_v exp(- integral_v^t lambda_u^y dif u) exp(- integral_v^t (lambda_u^y (ell_2; v)+ lambda_u^y) dif u) dif v dif s \
//         &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y + pi_u (a_1) lambda_u^(a) dif u)  exp(-integral_s^t lambda_u^y (ell_1; s) + lambda_u^y + pi_u (a_1) lambda_u^(a) dif u) dif s \
//             &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//     &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) \
//         &quad times integral_s^t (exp(- integral_s^v lambda_u^y dif u) - exp(- integral_s^v (lambda_u^y + lambda_u^ell) dif u)) dif (exp(- integral_v^t (lambda_u^y (ell_2; v)+ lambda_u^y) dif u) dif v) dif s \
//         &- integral_0^t (exp(-integral_0^s lambda_u^y + pi_u (a_1) lambda_u^(a) dif u) - exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u)) dif( exp(-integral_s^t lambda_u^y (ell_1; s) + lambda_u^y + pi_u (a_1) lambda_u^(a) dif u)) dif s \
// $

// Let there be constant intensities,
// i.e.,
// $
//     lambda_u^y = lambda^(y), \
//     lambda_u^y (ell_i; s) = lambda^(y,*) (ell), \
//     pi_u (a_1) = pi, \
//     lambda_u (a_1) = lambda^(a), \
//     lambda_u^ell = lambda^(ell).
// $
// This simplifies further to:
// $
//     &1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times integral_s^t exp(- (lambda^(y) + lambda^(ell)) (v-s)) lambda^(ell) exp(- lambda^(y,*) (ell) (t-v)) dif v dif s \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) lambda^(ell) exp(- lambda^(y,*) (ell) (t-s)) dif s \
//         &=1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times exp((lambda^y+ lambda^ell) s) exp(- lambda^(y,*) (ell) (t))  lambda^(ell) integral_s^t exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) v)  dif v dif s \
//         &- exp(- lambda^(y,*) (ell) t) lambda^(ell) (1- 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) exp (-(lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell))) \
//             &=1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times exp((lambda^y+ lambda^ell) s) exp(- lambda^(y,*) (ell) (t))  lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) (exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) s) - exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) t))  dif s \
//         &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) (1- exp (-(lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell))) \
    

// $
// Note that
// $
//     &integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times exp((lambda^y+ lambda^ell) s) exp(- lambda^(y,*) (ell) (t))  lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) (exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) s) - exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) t))  dif s \
//         &=exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) integral_0^t exp(- pi lambda^(a) s) pi lambda^(a) \
//         &quad times   (exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) s) - exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) t))  dif s \
//         &=pi lambda^(a) exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) integral_0^t exp(- (lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)) s)  \
//         &- pi lambda^(a) exp(- (lambda^(y) + lambda^ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) integral_0^t exp(-  pi lambda^a s)  \
//         &= pi lambda^(a) exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/((lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell))) (1- exp(- (lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)) t) \
//             &- pi lambda^(a) exp(- (lambda^(y) + lambda^ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/(pi lambda^a) (1- exp(-  pi lambda^a t)) \

// $
// Collecting the terms
// $
//     &1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times integral_s^t exp(- (lambda^(y) + lambda^(ell)) (v-s)) lambda^(ell) exp(- lambda^(y,*) (ell) (t-v)) dif v dif s \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) lambda^(ell) exp(- lambda^(y,*) (ell) (t-s)) dif s \
//         &=1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         & quad - pi lambda^(a) exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/((lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell))) (1- exp(- (lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)) t) \
//             &+ exp(- (lambda^(y) + lambda^ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) (1- exp(-  pi lambda^a t)) \
//             &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) (1- exp (-(lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell))) \
//             &=1 - exp(- (lambda^(y) + lambda^(ell)) t) (1 - lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) ) \
//             &- exp(- (lambda^(y) + pi lambda^a + lambda^ell) (t)) lambda^(ell) (1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) - 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) \
//                 &quad - pi lambda^(a) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/((lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)))) \
//             &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) (1 + pi lambda^(a) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) ) \
//             &=1 - exp(- (lambda^(y) + lambda^(ell)) t) (1 - lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) ) \
//             &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + lambda^ell)) 

// $
// which is constant in $pi$.
// If $lambda_u^y (ell_1; s) = lambda_u^y (ell_2; v) = lambda_u^y$, then this reduces to
// $
//        &1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) (exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) - exp(- integral_s^t (lambda_u^y) dif u)) dif s \
//            &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y dif u) dif s \
//            &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ exp(- integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) (exp(- integral_s^t (lambda_u^ell) dif u) - 1) dif s \
//            &- exp(- integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell dif s \
//     &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ exp(- integral_0^t lambda_u^y dif u) exp(- integral_0^t lambda_u^ell dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) lambda_s^(a) dif s \
//            &- exp(- integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) (lambda_s^ell + pi_s (a_1) lambda_s^(a)) dif s \
//     &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ exp(- integral_0^t lambda_u^y dif u) exp(- integral_0^t lambda_u^ell dif u) (1-exp(- integral_0^t (pi_u (a_1) lambda_u^(a)) dif u)) \
//            &- exp(- integral_0^t lambda_u^y dif u) (1-exp(- integral_0^t (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) \
//                &=     1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ exp(- integral_0^t lambda_u^y dif u) exp(- integral_0^t lambda_u^ell dif u)  \
//            &- exp(- integral_0^t lambda_u^y dif u) \

// $

// Let there be somewhat constant intensities,
// i.e.,
// $
//     lambda_u^y = lambda^(y), \
//     lambda_u^y (ell_i; s) = lambda^(y,*) (ell) u, \
//     pi_u (a_1) = pi, \
//     lambda_u (a_1) = lambda^(a), \
//     lambda_u^ell = lambda^(ell).
// $
// This simplifies further to:
// $
//     &1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times integral_s^t exp(- (lambda^(y) + lambda^(ell)) (v-s)) lambda^(ell) exp(- 1/2 lambda^(y,*) (ell) (t-v)^2) dif v dif s \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) lambda^(ell) exp(- 1/2 lambda^(y,*) (ell) (t-s)^2) dif s \
//         &=1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times exp((lambda^y+ lambda^ell) s) exp(- lambda^(y,*) (ell) (t))  lambda^(ell) integral_s^t exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) v)  dif v dif s \
//         &- exp(- lambda^(y,*) (ell) t) lambda^(ell) (1- 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) exp (-(lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell))) \
//             &=1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times exp((lambda^y+ lambda^ell) s) exp(- lambda^(y,*) (ell) (t))  lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) (exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) s) - exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) t))  dif s \
//         &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) (1- exp (-(lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell))) \
    

// $
// Note that
// $
//     &integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times exp((lambda^y+ lambda^ell) s) exp(- lambda^(y,*) (ell) (t))  lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) (exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) s) - exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) t))  dif s \
//         &=exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) integral_0^t exp(- pi lambda^(a) s) pi lambda^(a) \
//         &quad times   (exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) s) - exp(- (lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) t))  dif s \
//         &=pi lambda^(a) exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) integral_0^t exp(- (lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)) s)  \
//         &- pi lambda^(a) exp(- (lambda^(y) + lambda^ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) integral_0^t exp(-  pi lambda^a s)  \
//         &= pi lambda^(a) exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/((lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell))) (1- exp(- (lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)) t) \
//             &- pi lambda^(a) exp(- (lambda^(y) + lambda^ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/(pi lambda^a) (1- exp(-  pi lambda^a t)) \

// $
// Collecting the terms
// $
//     &1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) pi lambda^(a) \
//         &quad times integral_s^t exp(- (lambda^(y) + lambda^(ell)) (v-s)) lambda^(ell) exp(- lambda^(y,*) (ell) (t-v)) dif v dif s \
//         &- integral_0^t exp(- (lambda^(y) + pi lambda^(a) + lambda^(ell)) s) lambda^(ell) exp(- lambda^(y,*) (ell) (t-s)) dif s \
//         &=1 - exp(- (lambda^(y) + lambda^(ell)) t) \
//         & quad - pi lambda^(a) exp(- lambda^(y,*) (ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/((lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell))) (1- exp(- (lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)) t) \
//             &+ exp(- (lambda^(y) + lambda^ell) (t)) lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) (1- exp(-  pi lambda^a t)) \
//             &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) (1- exp (-(lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell))) \
//             &=1 - exp(- (lambda^(y) + lambda^(ell)) t) (1 - lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) ) \
//             &- exp(- (lambda^(y) + pi lambda^a + lambda^ell) (t)) lambda^(ell) (1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) - 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) \
//                 &quad - pi lambda^(a) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) 1/((lambda^(y) - lambda^(y,*) (ell) + pi lambda^a + lambda^(ell)))) \
//             &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + pi lambda^(a) + lambda^ell)) (1 + pi lambda^(a) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) ) \
//             &=1 - exp(- (lambda^(y) + lambda^(ell)) t) (1 - lambda^(ell) 1/(lambda^(y) - lambda^(y,*) (ell) + lambda^(ell)) ) \
//             &- exp(- lambda^(y,*) (ell) t) lambda^(ell) 1/((lambda^(y) - lambda^(y,*) + lambda^ell)) 

// $
// which is constant in $pi$.
// If $lambda_u^y (ell_1; s) = lambda_u^y (ell_2; v) = lambda_u^y$, then this reduces to
// $
//        &1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) (exp(- integral_s^t (lambda_u^y + lambda_u^ell) dif u) - exp(- integral_s^t (lambda_u^y) dif u)) dif s \
//            &- integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell exp(-integral_s^t lambda_u^y dif u) dif s \
//            &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ exp(- integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) pi_s (a_1) lambda_s^(a) (exp(- integral_s^t (lambda_u^ell) dif u) - 1) dif s \
//            &- exp(- integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) lambda_s^ell dif s \
//     &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ exp(- integral_0^t lambda_u^y dif u) exp(- integral_0^t lambda_u^ell dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) lambda_s^(a) dif s \
//            &- exp(- integral_0^t lambda_u^y dif u) integral_0^t exp(- integral_0^s (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) (lambda_s^ell + pi_s (a_1) lambda_s^(a)) dif s \
//     &= 1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ exp(- integral_0^t lambda_u^y dif u) exp(- integral_0^t lambda_u^ell dif u) (1-exp(- integral_0^t (pi_u (a_1) lambda_u^(a)) dif u)) \
//            &- exp(- integral_0^t lambda_u^y dif u) (1-exp(- integral_0^t (pi_u (a_1) lambda_u^(a) + lambda_u^ell) dif u) \
//                &=     1 - exp(- integral_0^t (lambda_u^y  + lambda_u^ell ) dif u) \
//            &+ exp(- integral_0^t lambda_u^y dif u) exp(- integral_0^t lambda_u^ell dif u)  \
//            &- exp(- integral_0^t lambda_u^y dif u) \

// $


// The difference can be written as
// $
//     mean(tilde(Q)) [Y_t] - mean(Q) [Y_t] &= integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) (1 - exp(- integral_0^s (pi_u (a_0) lambda_u^(a)) dif u)) lambda_s^y dif s \
//         &+ integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) (1 - exp(- integral_0^s (pi_u (a_0) lambda_u^(a)) dif u)) (pi_s (a_1) lambda_s^(a) \
//             &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//             &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//             &+integral_0^t exp(- integral_0^s (lambda_u^y + pi_u (a_1) lambda_u^(a)) dif u) pi_s (a_1) exp(- integral_0^s (pi_u (a_0) lambda_u^(a)) dif u) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //     &=integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) (exp(integral_0^s (pi_u (a_0) lambda_u^(a)) dif u) - 1) lambda_s^y dif s \
//         // &+ integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) (exp(integral_0^s (pi_u (a_0) lambda_u^(a)) dif u)-1) (pi_s (a_1) lambda_s^(a) \
//         //     &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //     &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) pi_s (a_0) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //     &=integral_0^t integral_0^s exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) (exp(integral_0^w (pi_u (a_0) lambda_u^(a) dif u)) pi_w (a_0) lambda_w^(a) dif w) lambda_s^y dif s \
//         //     &+ integral_0^t integral_0^s exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) (exp(integral_0^w (pi_u (a_0) lambda_u^(a) dif u)) pi_w (a_0) lambda_w^(a) dif w) (pi_s (a_1) lambda_s^(a) \
//         //     &quad times integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //         &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) pi_s (a_0) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s \
//         //         &=integral_0^t integral_w^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u)  lambda_s^y dif s exp(integral_0^w (pi_u (a_0) lambda_u^(a) dif u)) pi_w (a_0) lambda_w^(a) dif w \
//         //         &+ integral_0^t integral_w^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) integral_s^v exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v pi_s (a_1) lambda_s^(a) dif s \
//         //         &quad times (exp(integral_0^w (pi_u (a_0) lambda_u^(a) dif u)) pi_w (a_0) lambda_w^(a) )  dif w\
//         //     &- integral_0^t exp(- integral_0^s (lambda_u^y + lambda_u^(a)) dif u) pi_s (a_0) lambda_s^(a)  integral_s^t exp(- integral_s^v lambda_u^y dif u) lambda_v^y dif v dif s 
// $
If we could find an example where the above is non-zero, then we would by the construction
in "existence of counterfactuals" have found an example where Påls exchangeability does not hold and mine does. 

= Right-censoring
Now suppose that in addition to the processes we observe, we also observe a component $N^c (t)$
which counts whether or not the subject has dropped out of the study at time $t$.
$tau^C$ denotes the first time at which this process is non-zero. 
Now consider the weight process,
$
    W (t) = W^(g^*) (t) W^c (t)
$ <eq:generalW>
where $W^(g^*)$ denotes the previously studied weight process given in ???
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
    1. The $Q$-$cal(F)_t$ compensator of $N^a (dif t times dif x)$ is $pi^*_t (dif x) Lambda_P^a (dif t)$.
    2. The $Q$-$cal(F)_t$ compensator of $N^x$ is $Lambda_P^x$ for $x in {y, ell_1, dots, ell_k}$.
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

#theorem[
    Let $kappa_t$ be a (local) martingale with $Delta kappa_t >= -1$
    and $Delta kappa_t^* > -1$ if $t < tau^(g^*)$. Then, 
$
    W_t^* := cal(E) (kappa)_t = cal(E) (kappa)_t cal(E) (- bb(N)^a)_t 
$
    if and only if $Delta kappa_(tau^(g^*)) = -1$ whenever $tau^(g^*) < oo$.
]
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

Now, we consider only $kappa$'s of the form 
$
    kappa (t) = integral_0^t sum_(x in cal(A)) bb(1) {s <= t} tilde(h) (s, x) M^(a, x) (dif s)
$
with $tilde(h) (s, x)$ $P$-$cal(F)_t$ predictable
with the restriction stated in the above theorem.
We make this restriction as any reasonable exchangeability conditions
should be placed on the treatment process.

#theorem[
    Let $kappa_t = integral_0^t sum_(x in cal(A)) bb(1) {s <= t} tilde(h) (s, x) M^(a, x) (dif s)$
    for some $P$-$cal(F)_t$-predictable process $tilde(h) (s, x)$
    and that $Q_kappa (tau^(g^*) = oo) = 1$.
    Suppose that $Delta kappa_t >= -1$ and $Delta kappa_t^* > -1$ if $t < tau^(g^*)$
    and that $cal(E) (kappa)_t$ is a uniformly integrable $P$-$cal(F)_t$-martingale.
    Suppose that $cal(A) = {a_0, a_1}$ and that $pi_t^* (a_1) = 1$.
    Then any $kappa$ with $tilde(h) (s, a_1)$ a $P$-$cal(F)_t$-predictable process and
    $
        tilde(h) (s, a_0) =bb(1) {s <= tau^(g^*)} (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s))
    $
    will satisfy the condition 2. of @thm:identifiabilitygeneral. Moreover, this solution is unique in the sense that
    whenever $integral_0^t tilde(h) (s, a_0) M^(a, a_0) (dif s)$ is of finite variation,
    this is equal to
    $
        integral_0^t bb(1) {s <= tau^(g^*)} (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) M^(a, a_0) (dif s).
    $
    Conclude that, under regularity conditions,
    $
        cal(E) (kappa)_t &= 1 + integral_0^t cal(E) (kappa)_(s -) bb(1) {s <= tau^(g^*)} (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) M^(a, a_0) (dif s) \ 
            &+ integral_0^t cal(E) (kappa)_(s -) tilde(h) (s, a_1) M^(a, a_1) (dif s)
    $
    are all the solutions to condition 2. of @thm:identifiabilitygeneral,
    where $tilde(h) (s, a_1)$ is any $P$-$cal(F)_t$-predictable process, ensuring that $cal(E) (kappa)_t$ is a uniformly integrable $P$-$cal(F)_t$-martingale.
]
#proof[

//We also suppose that $Delta Lambda^(a, x)_t < 1$.
//This happens for example if $Delta Lambda^a_t < 1$.
The above theorem gives that we must have
$
    Delta kappa_(tau^(g^*)) = sum_(x in cal(A)) tilde(h) (tau^(g^*), x) Delta M^(a, x)_(tau^(g^*)) = -1
$
on the event that $tau^(g^*) < oo$.
Suppose that $cal(A) = {a_0, a_1}$
and that $pi_t^* (a_1) = 1$.
In this case, we can write the equation above as
$
    h(tau^(g^*), a_1) (0 - pi_(tau^(g^*)) (a_1) Delta Lambda^(a)_(tau^(g^*))) + h(tau^(g^*), a_0) (1 - (1- pi_(tau^(g^*)) (a_1)) Delta Lambda^(a)_(tau^(g^*))) = -1
$
or
$
    (h(tau^(g^*), a_0) - h(tau^(g^*), a_1)) pi_(tau^(g^*)) (a_1) Delta Lambda^(a)_(tau^(g^*)) + h(tau^(g^*), a_0) (1 - Delta Lambda^(a)_(tau^(g^*))) = -1
$
We consider various cases:
- Absolutely continuous case: $Delta Lambda^(a) equiv 0$.
- $macron(N)^a$ is $cal(F)_t$-predictable.
- Jump times for $macron(N)^a$ are discrete.
- General case.

== Absolutely continuous case <sec:absolutely_continuous_case>
In this case, conclude that $h(tau^(g^*), a_0) = -1$.
However, nothing else can be said about $h(tau^(g^*), a_1)$
as the equation does not place any other restrictions than
it being predictable.
We can, however, conclude that $integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) = integral_0^(t and tau^(g^*)) (-1) M^(a, a_0) (dif s) = - bb(N)^(a) (t) + bb(L)^(a) (t)$
whenever that integral happens to be of finite variation.
To see this, note that
$
    integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) &= integral_0^(t and tau^(g^*)) h(s, a_0) N^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) h(s, a_0) Lambda^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (-1) N^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) h(s, a_0) Lambda^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (-1) M^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) (h(s, a_0) + 1) Lambda^(a, a_0) (dif s),
$
meaning that $integral_0^(t and tau^(g^*)) (h(s, a_0) + 1) Lambda^(a, a_0) (dif s)$
is of finite variation, a local martingale, predicable and hence constant (and thus zero)
by Theorem 15, p. 115 of @protter2005stochastic.

== $macron(N)^a$ is $cal(F)_t$-predictable
Im this case, $Delta Lambda_t^a = Delta macron(N)_t^a$
which is 1 at $t = tau^(g^*)$.
Therefore,
$
    (h(tau^(g^*), a_0) - h(tau^(g^*), a_1)) pi_(tau^(g^*)) (a_1) = -1
$
or
$
    h(tau^(g^*), a_0) = h(tau^(g^*), a_1) - 1/(pi_(tau^(g^*)) (a_1))
$
Thus, we have
$
    K^(h)_t &= integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) + integral_0^(t and tau^(g^*)) h(s, a_1) M^(a, a_1) (dif s) \
        &= integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) (h(s, a_1)) M^(a, a_0) (dif s) + integral_0^(t and tau^(g^*)) (h(s, a_1)) M^(a) (dif s) \
        &= integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (- 1/(pi_(s) (a_1))) N^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) Lambda^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (- 1/(pi_(s) (a_1))) M^(a, a_0) (dif s) - integral_0^(t and tau^(g^*)) ((h(s, a_0)-h(s, a_1)) + 1/(pi_(s) (a_1))) Lambda^(a, a_0) (dif s) \
$
Assuming that $integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s)$ is of finite variation,
we have that $integral_0^(t and tau^(g^*)) ((h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s) = integral_0^(t and tau^(g^*)) (- 1/(pi_(s) (a_1))) M^(a, a_0) (dif s)$.
We conclude that $K^(h)_t$ if $integral_0^(t and tau^(g^*)) (h(s, a_0)-h(s, a_1)) M^(a, a_0) (dif s)$ is of finite variation
does not depend on the choice of $h$.
Therefore, the stochastic exponential $cal(E) (K^(h))_t$ does not depend on the choice of $h$ either,
and we may conclude that $cal(E) (K^(h))_t = cal(E) (K)_t$.

== General case
Suppose that $(1-pi_t (a_1)) Delta Lambda^(a)_(t) < 1$ for all $t > 0$.
Otherwise, an argument similar to the one we will give will split into cases.

We have that
$
    &(h(tau^(g^*), a_0) - h(tau^(g^*), a_1)) pi_(tau^(g^*)) (a_1) Lambda^(a) ({tau^(g^*)}) bb(1) {Lambda^(a) ({tau^(g^*)}) > 0} \
        &quad + h(tau^(g^*), a_0) (1 - Lambda^(a) ({tau^(g^*)})) bb(1) {Lambda^(a) ({tau^(g^*)}) > 0} \
        &quad + h(tau^(g^*), a_0) (bb(1) {Lambda^(a) ({tau^(g^*)}) = 0}) = -1
$

By the same argument as in the absolutely continuous case,
we have that
$
    &integral_0^(t and tau^(g^*)) h(s, a_0) bb(1) {Lambda^(a) ({s}) = 0} M^(a, a_0) (dif s) \
        &= - integral_0^(t and tau^(g^*)) bb(1) {Lambda^(a) ({s}) = 0} M^(a,a_0) (dif s) \
        &= - bb(N)^(a) (t) bb(1) {Lambda^(a) ({tau^(g^*)}) = 0} + bb(L)^(a, c) (t),
$
where $bb(L)^(a, c)$ is the continuous part of $bb(L)^a$.
Next whenever $Lambda^(a) ({tau^(g^*)}) > 0$, we find
$
    h(tau^(g^*), a_0) = (- 1 + h(tau^(g^*), a_1) pi_(tau^(g^*)) (a_1) Delta Lambda^(a)_(tau^(g^*))) / (1 - (1-pi_(tau^(g^*)) (a_1)) Delta Lambda^(a)_(tau^(g^*)))
$
Therefore, it will again be the case that
$
    &integral_0^(t and tau^(g^*)) h(s, a_0) bb(1) {Lambda^(a) ({s}) > 0} M^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (- 1 + h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1 - (1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) bb(1) {Lambda^(a) ({s}) > 0} M^(a, a_0) (dif s) \
$
Conclude that
$
    &integral_0^(t and tau^(g^*)) h(s, a_0) M^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) ((- 1 + h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1 - (1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) bb(1) {Lambda^(a) ({s}) > 0} - bb(1) {Lambda^(a) ({s}) = 0}) M^(a, a_0) (dif s) \
        &= integral_0^(t and tau^(g^*)) (- 1 + bb(1) {Lambda^(a) ({s}) > 0} h(s, a_1) pi_(s) (a_1) Delta Lambda^(a)_(s)) / (1-bb(1) {Lambda^(a) ({s}) > 0}(1-pi_(s) (a_1)) Delta Lambda^(a)_(s)) M^(a, a_0) (dif s),
$
and $h(dot,a_1)$ freely chosen, predictable satisfying some integrability criteria.
Interestingly, this means that the stochastic exponential $cal(E) (K^(h))_t$ will depend on the choice of $h$ in general,
but only through $h(s, a_1)$ which can be freely chosen.
]

// Note: Let us consider whether or not the potential outcome process exists.
// Using orthogonality, use latent variables C_k and (T_k, Delta_k) to get observed data.
// Note: Need to make sure that, earlier, 

// == Comparisons of the positivity assumptions in @ryalenPotentialOutcomes

// One may ask oneself if positivity holds in @ryalenPotentialOutcomes;
// under what assumptions does positivity in @thm:identifiabilitymartingale
// hold? In general, however, it would appear that the two positivity conditions
// are different and neither implies the other.

// Can we find a process $phi$ such that
// $cal(E) (K) =  (cal(E) (-bb(N)^a)) / (cal(E) (-bb(L)^a)) cal(E) (phi)$?

// #theorem[
//     $phi$ is given by
//         $
//             phi_t = K_t - bb(L)_t^a + bb(N)_t^a - [K, bb(L)^a]_t,
//         $
//     where $[dot, dot]$ denotes the quadratic covariation process (@protter2005stochastic),
//     where
//     $
//         [K, bb(L)^a]_t &= integral_0^(t and tau^(g^*)) sum_v bb(1) {event(v-1) < s <= event(v)} sum_(i != g^*_v (history(v-1), event(v))) pi_s ({a_j}) Delta Lambda^(a) (s) \
//             &qquad times sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) \
//     $
//     In the absolutely continuous case, $[K, bb(L)^a]_t = 0$ as $Delta Lambda^a_t = 0$ for all $t > 0$.
//     If, further, $pi_t^* ({a_j}) = 1$ for some $j$,
//     then
//     $
//         phi_t = integral_0^(t and tau^(g^*)) ((1)/(pi_s) - 1) M^(a, a_j) (dif s).
//     $
// ]
// #proof[
//     To this end, let $v := bb(1) {W(t) > 0, tilde(W) (t) > 0} = bb(1) {tau^(g^*) > t} = cal(E) (- bb(N)^a)$
//     and calculate 
// $
//     cal(E) (phi) v &= (cal(E) (K) cal(E) (- bb(L)^a)) / (cal(E) (- bb(N)^a)) v \
//         &= cal(E) (K) cal(E) (-bb(L)^a) v \
//         &= cal(E) (K - bb(L)^a - [K, bb(L)^a]) v \
//         &= cal(E) (K - bb(L)^a + bb(N)^a - [K, bb(L)^a]) v,
// $
// where the last equality follows since $bb(N)^a v equiv 0$.
// Note that
// $
//     [K, bb(L)^a]_t &= integral_0^t Delta bb(L)^a_s sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) \
//         &=^(*) integral_0^(t and tau^(g^*)) sum_v bb(1) {event(v-1) < s <= event(v)} sum_(i != g^*_v (history(v-1), event(v))) pi_s ({a_j}) Delta Lambda^(a) (s) \
//             &qquad times sum_(j=1)^k ((pi_s^* ({a_j}))/(pi_s ({a_j})) - 1) N^(a, a_j) (dif s) 
// $

// In the case where $Delta Lambda^a_s equiv 0$ and $pi_s^* ({a_j}) = 1$ for some $j$,
// then

// $
//     v(K_t - bb(L)_t^a + bb(N)_t^a) = v integral_0^(t and tau^(g^*)) ((1)/(pi_s) - 1) M^(a, a_j) (dif s)
// $
// and $[K, bb(L)^a]_t = 0$.
// ]

// A simple consequence of this is the following.
// Assume that $Q_"ryalen" << P$ with $Q_"ryalen" = (cal(E) (-bb(N)^a)) / (cal(E) (-bb(L)^a)) bullet P$.
// and, say, $cal(E) (phi)$ is a uniformly integrable $Q_"ryalen"$-$cal(F)_t$-martingale,
// i.e., that $Q << Q_"ryalen"$, then $Q_"ryalen" << P$ implies that $Q << P$.
// This happens for example if $cal(E) (phi)$ is uniformly bounded by a constant.


#bibliography("references/ref.bib",style: "apa")


