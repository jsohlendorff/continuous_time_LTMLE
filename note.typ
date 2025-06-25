
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
#import "@preview/colorful-boxes:1.4.3": *

#set footnote(numbering: "*")
#set cite(form: "prose")
#show ref: it => [#text(fill: blue)[#it]]
#show: arkheion.with(
    title: "A Novel Approach to the Estimation of Causal Effects of Multiple Event Point Interventions in Continuous Time",
    authors: (
        (name: "Johan Sebastian Ohlendorff", email: "", affiliation: "University of Copenhagen"),
        (name: "Anders Munch", email: "", affiliation: "University of Copenhagen"),
        (name: "Thomas Alexander Gerds", email: "", affiliation: "University of Copenhagen"),
    ),
    abstract: [In medical research, causal effects of treatments that may change over
            time on an outcome can be defined in the context of an emulated target
            trial. We are concerned with estimands that are defined as contrasts of
            the absolute risk that an outcome event occurs before a given time
            horizon $tau$ under prespecified treatment regimens. Most of the
            existing estimators based on observational data require a projection
            onto a discretized time scale @Rose2011. We consider a recently developed continuous-time approach to
            causal inference in this setting @rytgaardContinuoustimeTargetedMinimum2022, 
            which theoretically allows preservation of the precise event timing on a
            subject level. Working on a continuous-time scale may improve the
            predictive accuracy and reduce the loss of information. However,
            continuous-time extensions of the standard estimators comes at the cost
            of increased computational burden. We will discuss a new
            sequential regression type estimator for the continuous-time framework
            which estimates the nuisance parameter models by backtracking through
            the number of events. This estimator significantly reduces the
            computational complexity and allows for efficient, single-step targeting
            using machine learning methods from survival analysis and point
            processes, enabling robust continuous-time causal effect estimation.
    ]
)

#set page(margin: (left: 10mm, right: 10mm, top: 25mm, bottom: 30mm))
#show math.equation: set text(9pt)
#set math.equation(numbering: "(1)")
//#show: equate.with(breakable: true, sub-numbering: true)

#show math.equation: it => {
  if it.block and not it.has("label") [
    #counter(math.equation).update(v => v - 1)
    #math.equation(it.body, block: true, numbering: none)#label("")
  ] else {
    it
  }  
}

#show: thmrules.with(qed-symbol: $square$)

// = TODO

// - [/] Identifiability under censoring
// - [ ] Simulation study (ML?).
// - [ ] Application to real data (e.g., EHR data).
// - [/] Comparison of EIF and target parameter with @rytgaardContinuoustimeTargetedMinimum2022.
// - [ ] Consistency of variance estimator?
// - [ ] Empirical process conditions 
// - [/] Cross-fitting
// - [x] Discussion. Bayesian approach + pooling/rare events. 

= Introduction
Randomized controlled trials (RCTs) are widely regarded as the gold standard for estimating the causal effects of treatments on clinical outcomes.
However, RCTs are often expensive, time-consuming, and in many cases infeasible or unethical to conduct.
As a result, researchers frequently turn to observational data as an alternative.
Even in RCTs, challenges such as treatment noncompliance and time-varying confounding — due to factors like side effects or disease progression — can complicate causal inference.
In such cases, one may be interested in estimating the effects of initiating or adhering to treatment over time.

Marginal structural models (MSMs), introduced by @robins1986, are a widely used approach for estimating causal effects from observational data, particularly in the presence of time-varying confounding and treatment.
MSMs typically require that data be recorded on a discrete time scale, capturing all relevant information available to the clinician at each treatment decision point and for the outcome.

However, many real-world datasets — such as health registries — are collected in continuous time, with patient characteristics updated at irregular, subject-specific times.
These datasets often include detailed, timestamped information on events and biomarkers, such as drug purchases, hospital visits, and laboratory results.
Analyzing data in its native continuous-time form avoids the need for discretization, which can introduce bias and increase variance depending on the choice of time grid (@ryalen2019additive @discretization2020guerra).

In this paper, we consider a longitudinal continuous-time framework similar to that of @rytgaardContinuoustimeTargetedMinimum2022.
Like @rytgaardContinuoustimeTargetedMinimum2022, we adopt a nonparametric approach and focus on estimation and inference through the efficient influence function, yielding nonparametrically locally efficient estimators via a one-step procedure.

To this end, we propose an inverse probability of censoring iterative conditional expectation (ICE-IPCW) estimator, which, like that of  @rytgaardContinuoustimeTargetedMinimum2022,
iteratively updates nuisance parameters.
A key innovation in our method is that these updates are performed by indexing backwards through the number of events rather than through calendar time.
Moreover, our estimator addresses challenges associated with the high dimensionality of the target parameter by employing inverse probability of censoring weighting (IPCW).
The distinction between event-based and time-based updating is illustrated in @fig:timegridrytgaard and @fig:eventgrid.
To the best of our knowledge, no general estimation procedure has yet been proposed for the components involved in the efficient influence function.

Continuous-time methods for causal inference in event history analysis have also been explored by @roysland2011martingale and @lok2008.
@roysland2011martingale developed identification criteria using a formal martingale framework based on local independence graphs,
enabling causal effect estimation in continuous time via a change of measure. @lok2008 similarly employed a martingale approach but focused on structural nested models to estimate a different type of causal parameter—specifically,
a conditional causal effect. However, such estimands may be more challenging to interpret than marginal causal effects.

A key challenge shared by these approaches is the need to model intensity functions,
which can be difficult to estimate accurately.
While methods such as Cox proportional hazards (@cox1972) and Aalen additive hazards (@aalen1980model) are commonly used for modeling intensities,
they are often inadequate in the presence of time-varying confounding, as they do not naturally account for the full history of time-varying covariates.
Consequently, summary statistics of covariate history are typically used to approximate the intensity functions.

In this paper, we propose a simple solution to this issue for settings with a limited number of events.
Our approach enables the use of existing regression techniques from the survival analysis and point process literature to estimate the necessary intensities, providing a practical and flexible alternative.

//and propose the inverse probability of censoring weighting iterated conditional expectations
//estimator (ICE-IPCW).
//Let $kappa_i (tau)$ be the number of events for individual $i$ up to time $tau$.
//In @rytgaardContinuoustimeTargetedMinimum2022, the authors propose a continuous-time LTMLE for the estimation of causal
//effects in which a single step of the targeting procedure must update each of the nuisance estimators $sum_(i = 1)^n kappa_i (tau)$ times.

//Furthermore, continuous-time data captures more precise information about when events occur, which may be valuable in a predictive sense.

#figure(timegrid(new_method: false), caption:  [The figure illustrates the sequential regression approach
    given in @rytgaardContinuoustimeTargetedMinimum2022 for two observations:
    Let $t_1 < dots < t_m$ be all the event times in the sample.
    Let $P^(G^*)$ denote the interventional probability measure.
    Then, given $mean(P^(G^*))[Y | cal(F)_(t_(r))]$,
    we regress back to $mean(P^(G^*))[Y | cal(F)_(t_(r-1))]$ (through multiple regressions).
],) <fig:timegridrytgaard>

#figure(timegrid(new_method: true), caption: [The figure illustrates the sequential regression approach
    proposed in this article. For each event number $k$ in the sample, we regress back on the history $history(k-1)$.
    Let $P^(G^*)$ denote the interventional probability measure.
    That is, given $mean(P^(G^*))[Y | history(k)]$,
    we regress back to $mean(P^(G^*))[Y | history(k-1)]$.
    In the figure, $k=3$. The difference is that we employ the stopping time $sigma$-algebra $history(k)$ here
    instead of the filtration $cal(F)_(t_(r))$.
],) <fig:eventgrid>

= Setting and Notation

Let $tauend$ be the end of the observation period.
We will focus on the estimation of the interventional absolute risk in the presence of time-varying confounding at a specified time horizon $tau < tauend$.
We let $(Omega, cal(F), P)$ be a statistical experiment on which all processes
and random variables are defined. 

At baseline,
we record the values of the treatment $treat(0)$ and the time-varying covariates $covariate(0)$
and let $cal(F)_0 = sigma(treat(0), covariate(0))$ be the $sigma$-algebra corresponding
to the baseline information.
//The time-varying covariates may principally include covariates
//which do not change over time, but for simplicity of notation, we will include them among
//those that do.
It is not a loss of generality to assume that we have two treatment options over time so that $A(t) in {0, 1}$ (e.g., placebo and active treatment),
where $A(t)$ denotes the treatment at time $t>=0$.
//#footnote[More generally, we allow a finite number of values for treatment; there is no loss of generality in assuming that $A$ is one-dimensional].
The time-varying confounders $L(t)$ at time $t>0$ are assumed
to take values in a finite subset $cal(L) subset RR^m$,
so that $L(t) in cal(L)$ for all $t >= 0$.
We assume that the stochastic processes $(L(t))_(t>=0)$ and $(A(t))_(t>=0)$ are càdlàg (right-continuous with left limits),
jump processes.
Furthermore, we require that the times at which the treatment and covariate values may change 
are dictated entirely by the counting processes $(N^a (t))_(t>=0)$ and $(N^ell (t))_(t>=0)$, respectively
in the sense that $Delta A (t) != 0$ only if $Delta N^a (t) != 0$ and $Delta L (t) != 0$ only if $Delta N^ell (t) != 0$.
We _emphasize_ the importance of this assumption:
Random changes of covariate values $L$ and treatment $A$ may only happen at a possibly random discrete set of time points.
For technical reasons and ease of notation, we shall assume that the number of jumps $K(t)$ at time $t$
for the processes $L$ and $A$ satisfies $K(tauend) <= K - 1$ $P$-a.s. for some finite $K >= 1$.
// If K(tauend) denotes the total number of events in the sample (random variable). Then we assume that K(tauend) <= K
// However, this might be relaxed to E[K(tauend)] < oo, i.e., the expected number of events is finite.

We also have counting processes representing
the event of interest $(N^y (t))_(t>=0)$ and the competing event $(N^d (t))_(t>=0)$.
Let $N^c$ be the censoring process.
Initially, we shall allow only administrative censoring, i.e., $N^c (t) = bb(1) {t > tauend}$ for all $t >= 0$. 
//Finally, let $N^c$ be the counting process for the censoring counting process.
For all counting processes involved, we assume for simplicity that the jump times differ with probability 1 (i.e., if $x!=y$, we have $Delta N^x Delta N^y eq.triple 0$.).
This is not a limiting assumption for real data as events are never truly simultaneous.
//Moreover, we assume that only a bounded number of events occur for each individual in the time interval $[0, tauend]$ (@assumptionbounded).
Thus, we have observations from a jump process $alpha(t) = (N^a (t), A (t), N^ell (t), L(t), N^y (t), N^d (t))$,
and the natural filtration $(cal(F)_t)_(t>=0)$ is given by $cal(F)_t = sigma (alpha(s) | s <= t) or cal(F)_0$.
Let $event(k)$ be the $k$'th ordered jump time of $alpha$, that is $T_0 = 0$ and $event(k) = inf {t > event(k-1) | alpha (t) != alpha (event(k-1))} in [0, oo]$ be the time of the $k$'th event
and let $status(k) in {c, y, d, a, ell}$ be the status of the $k$'th event, i.e., $status(k) = x$ if $Delta N^x (event(k)) = 1$.
We let $event(k+1) = oo$ if $event(k) = oo$ or $status(k-1) in {y, d, c}$.
As is common in the point process literature, we define $status(k) = Ø$
if $event(k) = oo$ or $status(k-1) in {y, d,c }$ for the empty mark. 

//We also impose the condition that the last event has to be a terminal event, i.e., $status(K) = y$ or $d$.
We let $treat(k)$ ($covariate(k)$) be the treatment (covariate values) at the $k$'th event, i.e., $treat(k) = A(event(k))$ if $status(k) = a$ ($covariate(k) = L(event(k))$ if $status(k) = ell$)
and $treat(k) = A(event(k-1))$ ($covariate(k) = L(event(k-1))$) otherwise.
If $event(k-1) = oo$, $status(k-1) in {y, d, c}$, or $status(k) in {y, d, c}$, we let $treat(k) = Ø$ and $covariate(k) = Ø$.
To the process $(alpha(t))_(t>=0)$, we associate the corresponding random measure $N^alpha$ on $(RR_+ times ({a, ell, y, d, c} times {0,1} times cal(L)))$ by

$
    N^alpha (dif (t, x, a, ell)) = sum_(k: event(k) < oo) delta_((event(k), status(k), treat(k), covariate(k))) (d (t, x, a, ell)),
$
where $delta_x$ denotes the Dirac measure on $(RR_+ times ({a, ell, y, d, c} times {0,1} times cal(L)))$.
It follows that the filtration $(cal(F)_t)_(t>=0)$ is the natural filtration of the random measure $N^alpha$.
Thus, the random measure $N^alpha$ carries the same information as the stochastic process $(alpha(t))_(t>=0)$.
This will be critical for dealing with right-censoring.

//Note that also by @assumptionbounded, this means that there exists a compensator $Lambda$ such that
//$
//    N (d (t, x, a, ell)) - Lambda (d (t, x, a, ell))
//$
//is a martingale with respect to the filtration $(cal(F)_t)_(t>=0)$.
// E N_t < oo
//Since the filtration is the natural filtration, it follows that the stopping time

We observe $O= (event(K), status(K), treat(K-1), covariate(K-1), event(K-1), status(K-1), dots, treat(0), covariate(0)) ~ P in cal(M)$ where
$cal(M)$ is the statistical model, i.e., a set of probability measures
and obtain a sample $O = (O_1, dots, O_n)$ of size $n$.
For a single individual, we might observe $treat(0) = 0$ and $covariate(0) = 2$,
 $treat(1) = 1$, $covariate(1) = 2$, $event(1) = 0.5$, and $status(1) = a$,
$treat(2) = 1$, $covariate(2) = 2$, $event(2) = 1.5$, and $status(2) = y$,
and $event(3) = oo$, $status(3) = Ø$, so $K(t) = 2$ for that individual.
Another person might have $status(1) = d$ and so $K(t) = 0$ for that individual.
For the confused reader, we refer to @fig:longitudinaldatalong,
which gives the long format of a hypothetical longitudinal dataset
with time-varying covariates and treatment registered at irregular time points,
and its conversion to wide format in @fig:longitudinaldatawide,
representing the data set in the form of $O$.

#show table.cell.where(y: 0): strong
#set table(
  stroke: (x, y) => if y == 0 {
    (bottom: 0.7pt + black)
  } else if x==0 {
    (right: 0.1pt + black)
  },
  align: (x, y) => (
    if x > 0 { center }
    else { left }
  )
)

#figure(table(
            columns: (auto, auto, auto, auto, auto),
            inset: 10pt,
            align: horizon,
            table.header(
                [id], [time], [event], [$L$], [$A$],
            ),
                [1], [0], [baseline], [2], [1],
    [1], [0.5], [visitation time; stay on treatment], [2], [1],
    [1], [8], [primary event], [Ø], [Ø],
    [2], [0], [baseline], [1], [0],
    [2], [10], [primary event], [Ø], [Ø],
    [3], [0], [baseline], [3], [1],
    [3], [2], [side effect ($L$)], [4], [1],
    [3], [2.1], [visitation time; discontinue treatment], [4], [0],
        [3], [5], [primary event], [Ø], [Ø]
        ),
            caption: [
                An example of a longitudinal dataset from electronic health records or a clinical trial with $tauend = 15$
                with $K=2$ for $n=3$ (3 observations). Here, the time-varying covariates only have dimension 1.
                Events are registered at irregular/subject-specific time points
                and are presented in a long format. Technically, though, events at baseline are not to be considered events, but we include them here for completeness.
            ]
        ) <fig:longitudinaldatalong>

#figure(table(
    columns: (auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto),
                inset: 10pt,
            align: horizon,
    table.header(
        [id], [$covariate(0)$], [$treat(0)$], 
        [$covariate(1)$], [$treat(1)$], [$event(1)$], [$status(1)$],
        [$covariate(2)$], [$treat(2)$], [$event(2)$], [$status(2)$],
        [$event(3)$], [$status(3)$]
    ),
    [1], [2], [1], [2], [1], [0.5], [$a$], [Ø], [Ø], [8], [$y$], [$oo$], [Ø],
    [2], [1], [0], [Ø], [Ø], [10], [$y$], [Ø], [Ø], [$oo$], [Ø], [$oo$], [Ø],
    [3], [3], [1], [4], [1], [2], [$ell$], [4], [0], [2.1], [$a$], [$5$], [$y$],
                ),
                caption: [
                The same example as in @fig:longitudinaldatalong, but presented in a wide format.
                ])<fig:longitudinaldatawide>

We will also work within the so-called canonical setting for technical reasons (@last1995marked, Section 2.2).
Intuitively, this means that we assume that $P$ defines only the distribution for the sequence of random variables given by $O$
and that we work with the natural filtration $(cal(F)_t)_(t>=0)$ generated by the random measure $N^alpha$.
// Formally, we take $Omega = RR times RR^d times N_(bold(X))$ (since $A$ is $bb(R)$-valued and $L$ is $bb(R)^d$-valued) and $cal(F) = cal(B)(RR times RR^d) times.circle cal(N)_(bold(X))$,
// where $bold(X)={a, ell, y, d, c} times RR times RR^d$ denotes the mark space and
// $cal(N)_(bold(X))$ denotes the $sigma$-algebra $cal(B) ((RR^+ times bold(X))^(K))$.
// Here $cal(B) (X)$ denotes the Borel $sigma$-algebra on $X$.
This is needed to ensure the existence of compensators can be explicitly written via by the regular conditional distributions of the jump times and marks,
but also to ensure that $history(k) = sigma(event(k), status(k), treat(k-1), covariate(k-1)) or history(k-1)$
and $cal(F)_0 = sigma(treat(0), covariate(0))$, where
$history(k)$ stopping time $sigma$-algebra $history(k)$ -- representing the information up to and including the $k$'th event -- associated with
stopping time $event(k)$.
We will interpret $history(k)$ as a random variable instead of a $sigma$-algebra, whenever it is convenient to do so and also make the implicit assumption that whenever we condition on $history(k)$,
we only consider the cases where $event(k) < oo$ and $status(k) in {a, ell}$.

Let $densitytrt(t, k)$ be the probability of being treated at the $k$'th event given $status(k) =a, event(k) = t$, and $history(k-1)$.
Similarly, let $densitycov(t, dot, k)$ be the probability measure for the covariate value given $status(k) = ell, event(k) = t$, and $history(k-1)$.
Let also $cumhazard(k, x, dif t)$ be the cumulative cause-specific hazard measure (see e.g., Appendix A5.3 of @last1995marked).
Note that in many places, we will not distinguish between $cumhazard(k, x, (0, t])$ and $cumhazard(k, x, t)$.
At baseline, we let $pi_0 (covariate(0))$ be the probability of being treated given $covariate(0)$
and $mu_0 (dot)$ be the probability measure for the covariate value.


//#footnote[Let $T in (0, oo]$ and $X in cal(X)$ be random variables. Then the cause-specific cumulative hazard measure is given by
//    $Lambda_x (dif t) = bb(1) {P(T >= t} > 0} P(T in dif t, X = x) / P(T >= t)$ (Appendix A5.3 of @last1995marked).] for the $k$'th event of type $x$ given $history(k-1)$.

= Estimand of interest and iterative representation <section:estimand>

We are interested in the causal effect of a treatment regime $g$ on the cumulative incidence function of the event of interest $y$ at time $tau$.
We consider regimes which naturally act upon the treatment decisions
at each visitation time but not the times at which the individuals
visit the doctor. 
The treatment regime $g$ specifies for each event $k = 1, dots, K-1$
with $status(k) = a$ (visitation time) the probability that
a patient will remain treated until the next visitation time via 
$pi_k^* (event(k), history(k-1))$ and at $k=0$ the
initial treatment probability $pi_0^* (covariate(0))$.

We first define a _version_ of the likelihood ratio
process,
// #footnote[
//     This is is motivated by the following fact: A compensator of the representing $N^a (dif (t, a))$ (counting the treatment events)
//     is given by
//     $
//         Lambda^a (dif (t, a)) = sum_(k=1)^(K-1) bb(1) {event(k-1) < t <= event(k)} (densitytrt(event(k), k))^(treat(k)) (1-densitytrt(event(k), k))^(1-treat(k)) cumhazard(k, a, dif s)
//     $
//     and so if we let $P^(G^*) (dif omega) = W^g (tauend, omega) P(dif omega)$,
//     we find under the assumption that $P^(G^*)$ defines a probability measure that in the measure $P^(G^*)$, a version of the compensator of $N^a$ is
//     given by
//     $
//         Lambda^a (dif (t, a)) = sum_(k=1)^(K-1) bb(1) {event(k-1) < t <= event(k)} (densitytrtint(event(k), "", k))^(treat(k)) (1-densitytrtint(event(k), "", k))^(1-treat(k)) cumhazard(k, a, dif s)
//     $
//     corresponding to plugging in the intervention probabilities $pi_k^* (event(k), history(k-1))$ instead of $pi_k (event(k), history(k-1))$
//     in the compensator. All other compensators remain the same which is the intuition behind the _g-formula_ (@RobinsLongitudinal2001 @robins1986)
// as discussed in @rytgaardContinuoustimeTargetedMinimum2022]
$
    W^g (t) = product_(k=1)^(N_t) ((densitytrtint(event(k), "", k)^(treat(k)) (1-densitytrtint(event(k), "", k))^(1-treat(k))) / (densitytrt(event(k), k)^(treat(k)) (1-densitytrt(event(k), k))^(1-treat(k))))^(bb(1) {status(k) = a}) (pi^*_0 (covariate(0))^(A(0)) (1-pi^*_0 (covariate(0)))^(1-A(0)))/ (pi_0 (covariate(0))^(A(0)) (1-pi_0 (covariate(0)))^(1-A(0))),
$ <eq:weightprocess>
where $N_t = sum_k bb(1) {event(k) <= t}$ is random variable denoting the number of events up to time $t$.
If we define the measure $P^(G^*)$ by the density, 
$
    (dif P^(G^*))/(dif P) (omega) = W^g (tauend, omega), omega in Omega,
$
representing the interventional world in which the doctor assigns treatments according to the probability measure $pi^*_k (event(k), history(k-1))$ for $k = 0, dots, K-1$,
then our target parameter is given by the mean interventional cumulative incidence function at time $tau$,
$
    Psi_tau^g (P) = mean(P^(G^*)) [N^y (tau)] =  mean(P) [N^y (tau) W^g (tau)],
$ <eq:identification>
where $N^y (t) = sum_(k=1)^K bb(1) {event(k) <= t, status(k) =y}$.
In our application, $pi_k^*$ may be chosen arbitrarily,
so that, in principle, _stochastic_, _dynamic_, and _static_ treatment regimes
can be considered.
However, for simplicity of presentation, we use the static observation plan $pi^*_0 (covariate(0)) = 1$ and $pi^*_k (event(k), history(k-1)) = 1$ for all $k = 1, dots, K-1$,
and the methods we present can easily be extended to more complex treatment regimes
and contrasts.
In this paper, we will assume that @eq:identification
causally identifies the estimand of interest.

// #footnote[
//     We can choose a compensator $Lambda^a (dif (t, a))$ of
//     $N^a (dif (t, a)) = sum_(k=1)^(K-1) bb(1) {event(k-1) < t <= event(k)} bb(1) {status(k) = a} delta_((event(k), treat(k-1)) (dif (t, a))$
//     such that
//     $
//         Lambda^a (dif (t, a)) =  sum_(k=1)^(K-1) bb(1) {event(k-1) < t <= event(k)} (densitytrt(s, k))^(treat(k)) (1-densitytrt(s, k))^(1-treat(k)) cumhazard(k, a, dif s),
//     $]
//     We can choose a compensator of $N^a (dif (t, a))$
//     such that 
// Define $P^(G^*) (dif omega) = W^g (tauend, omega) P(dif omega)$,...
// t
//    Note that by fifth equality of Apppendix S1.2 of @rytgaardContinuoustimeTargetedMinimum2022,
//    this is the same as the target parameter in @rytgaardContinuoustimeTargetedMinimum2022 with no competing event.

We now present a simple iterated representation of the data target parameter $Psi_tau^g (P)$ in the case with no censoring.
To do so, define
$
    S_k (t | history(k-1)) = product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) Lambda_k^x (dif s | history(k-1))), k = 1, dots, K
$
where $product_(s in (0, t])$ is the product integral over the interval $(0, t]$ (@gill1990survey).

Our idea builds upon the works of @bangandrobins2005 (in discrete time) and @rytgaardContinuoustimeTargetedMinimum2022 (in continuous time),
who suggest the use of so-called _iterated regressions_ of the target parameter.
We discuss more thoroughly the implications for inference of this representation, the algorithm for estimation and examples in @section:censoring
where we also deal with right-censoring.

#theorem[
    Let $Qbar(K) = bb(1) {event(K) <= tau, status(K) = y}$ and 
    $
        Qbar(k-1) (history(k-1)) &= mean(P) [bb(1) {event(k) <= tau, status(k) = ell) Qbar(k) (treat(k-1), covariate(k), event(k), status(k), history(k-1)) \
            &qquad+ bb(1) {event(k) < tau, status(k) = a) Qbar(k) (1, covariate(k-1), event(k), status(k), history(k-1)) \
            &qquad+ bb(1) {event(k) < tau, status(k) = y) mid(|) history(k-1)], 
    $ <eq:iterative>
    for $k = K, dots, 1$.
    Then,
    $
        Psi_tau^g (P) = mean(P) [Qbar(0) (1, covariate(0))].
    $ <eq:baselineQ>
    
    Furthermore,
    $
        Qbar(k-1) (history(k-1)) &= p_(k-1,a) (tau | history(k-1))  + p_(k-1,ell) (tau | history(k-1)) + p_(k -1,y) (tau | history(k-1)) \
    $ <eq:cuminc>
    where,
    $
        p_(k-1,a) (t | history(k-1)) &= integral_((event(k-1),t)) S_k (s- | history(k-1)) Qbar(k) (1, covariate(k-1), s, a, history(k-1)) cumhazard(k, a, dif s) \
        p_(k-1, ell) (t | history(k-1)) &= integral_((event(k-1),t)) S_k (s- | history(k-1)) \
            &qquad (mean(P) [Qbar(k) (treat(k-1), covariate(k), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] ) cumhazard(k, ell, dif s) \
            p_(k-1, y) (t | history(k-1)) &= integral_((event(k-1),t]) S_k (s- | history(k-1)) cumhazard(k, y, dif s), quad t <= tau.
    $
    
]<thm:parameter>

#proof[
    Let $W_(k, j) = (W^g (event(j))) / (W^g (event(k)))$ for $k < j$ (defining $0/0 = 0$).
    //For brevity of notation, we do not write $bb(1) {event(k-1) < oo and status(k-1) in {a, ell})$.
    We show that 
    $
        Qbar(k) = mean(P) [sum_(j=k+1)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | history(k)]
    $
    for $k = 0, dots, K$ satisfies the desired property of @eq:iterative.
    //First note that the $macron(Q)_k$ only need to be evaluated when the person is at risk. 
    First, we find
    $
        Qbar(k) &= mean(P) [sum_(j=k+1)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | history(k)] \
            &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} W_(k,k+1) \
                &#h(2cm)+ bb(1) {event(k+1) < tau, status(k+1) in {a, ell}} mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)])\
            &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} W_(k,k+1) \
                &#h(2cm)+ bb(1) {event(k+1) < tau, status(k+1) = a}  mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)] \
                &#h(2cm)+ bb(1) {event(k+1) < tau, status(k+1) = ell}  mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k))
                mid(|) history(k)] \
            &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} \
                &#h(2cm)+ bb(1) {event(k+1) < tau, status(k+1) = a}  mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)] \
                &#h(2cm)+ bb(1) {event(k+1) < tau, status(k+1) = ell}  mean(P) [mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)]
                mid(|) history(k)) \
            &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} \
                &#h(2cm)+ bb(1) {event(k+1) < tau, status(k+1) = a}  mean(P) [W_(k,k+1) Qbar(k+1) (treat(k+1), covariate(k), event(k), status(k), history(k)) | event(k+1), status(k+1), history(k)] \
                &#h(2cm)+ bb(1) {event(k+1) < tau, status(k+1) = ell} mean(P) [Qbar(k+1) (treat(k), covariate(k+1), event(k), status(k), history(k)) | event(k+1), status(k+1), history(k)] | history(k)) \
            &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} \
                &#h(2cm)+ bb(1) {event(k+1) < tau, status(k+1) = a}  mean(P) [W_(k,k+1) Qbar(k+1) (treat(k+1), covariate(k), event(k), status(k), history(k)) | event(k+1), status(k+1), history(k)] \
                &#h(2cm)+ bb(1) {event(k+1) < tau, status(k+1) = ell} Qbar(k+1) (treat(k), covariate(k+1), event(k), status(k), history(k)) | history(k)) \
    $ <eq:iterativeProof>
    by the law of iterated expectations and that
    $
        (event(k) <= tau, status(k) = y) subset.eq (event(j) < tau, status(j) in {a, ell})
    $
    for all $j = 1, dots, k-1$ and $k = 1, dots, K$. The first desired statement about $Qbar(k)$ simply follows from the fact that
    $
        &mean(P) [W_(k-1,k) Qbar(k) (treat(k), covariate(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = a, history(k-1)] \
            &= mean(P) [(bb(1) {treat(k) = 1})/(densitytrt(event(k), k)) Qbar(k) (1, covariate(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = a, history(k-1)] \
            &= mean(P) [(mean(P) [bb(1) {treat(k) = 1} | event(k), status(k) =a, history(k-1)])/(densitytrt(event(k), k))  Qbar(k) (1, covariate(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = a, history(k-1)] \
            &= mean(P) [Qbar(k) (1, covariate(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = a, history(k-1)] \
            &= Qbar(k) (1, covariate(k-1), event(k), status(k), history(k-1))
    $
    by the law of iterated expectations in the second step from which @eq:iterative follows.
    A similar calculation shows that $Psi_tau^g (P) = mean(P) [Qbar(0) (1, covariate(0))]$
    and so @eq:baselineQ follows.
    This shows the first statement.
    
    We now show the second statement.
    Since $cumhazard(k, x, dif t)$ is the cumulative cause-specific hazard given $history(k-1)$ and that the event was of type $x$,
    it follows that (A5.29 of @last1995marked)
    $
        P ((event(k), status(k)) in d(t,m) | history(k-1)) = sum_(x=a,ell,d,y) delta_x (dif m) prodint2(s, event(k-1), t) (1 - sum_(x = ell, a, d, y) cumhazard(k, x,dif s)) cumhazard(k, z,dif t), 
    $ <eq:densityProofICE>
    whenever $event(k-1) < oo$ and $status(k-1) in {a, ell}$, so
    we get @eq:cuminc by plugging in @eq:densityProofICE to the second last equality of @eq:iterativeProof.
] 

Two approaches are suggested by @thm:parameter.
The representation in @thm:parameter has a natural interpretation:
$Qbar(k)$ is the counterfactual probability of the primary event occuring at or before time $tau$
given the history up to and including the $k$'th event (among the people who are at risk of the event before time $tau$ after $k$ events).
@eq:iterative then suggests that we can estimate $Qbar(k-1)$ via $Qbar(k)$
by considering what has happened as the $k$'th event:
For each individual in the sample, we calculate the integrand in @eq:iterative depending on their value of $event(k)$ and $status(k)$,
and apply the treatment regime as specified by $pi_k^*$ if the individuals event is a treatment event.
Then, we regress these values directly on $(treat(k-1), covariate(k-1), event(k-1), status(k-1), dots, treat(0), covariate(0))$
to obtain an estimator of $Qbar(k-1)$.
On the other hand, we do not recommend using @eq:cuminc directly,
which involves iterative integration, as this method becomes computationally infeasible even for small values of $K$.

//The second representation (@eq:cuminc) is not important to us now,
//but we will use this representation later.
A benefit of this representation compared to full inverse probability weighting,
where we also weight with treatment propensities,
is that the estimator may be more stable
in the case of small estimated treatment propensities.

= Censoring <section:censoring>

In this section, we allow for right-censoring. That is, we introduce a right-censoring time $C>0$
at which we stop observing the multivariate jump process
$alpha$. We will introduce the notation necessary to
discuss the algorithm for the the ICE-IPCW estimator in @alg:ipcwice
and later discuss the assumptions necessary for consistency of the ICE-IPCW estimator
in @section:conditions.
In the remainder of the paper,
we will assume that $C != event(k)$ for all $k$ with probability 1.
As before, we let $(event(k), status(k), treat(k), covariate(k))$ be
the event times and marks for the $N^alpha$ process. 

Let $(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k))$ for $k=1, dots, K$ be the observed data given by 
$
    eventcensored(k) &= C and event(k) \
    statuscensored(k) &= cases(status(k) "if" C > event(k), "c" "if" C <= event(k) "and" statuscensored(k-1) != c, Ø "otherwise") \
    treatcensored(k) &= cases(treat(k)"if" C > event(k), Ø "otherwise") \
    covariatecensored(k) &= cases(covariate(k) "if" C > event(k), Ø "otherwise")
$ <eq:observedata>
for $k = 1, dots, K$,
and let $historycensored(k)$ heuristically be defined by
$
    historycensored(k) = sigma(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k), dots, eventcensored(1), statuscensored(1), treatcensored(1), covariatecensored(1), treat(0), covariate(0)),
$ <eq:ftkcens>
defining the observed history up to and including the $k$'th event.
Thus $O=(eventcensored(1), statuscensored(1), treatcensored(1), covariatecensored(1), dots, eventcensored(K), statuscensored(K), treatcensored(K), covariatecensored(K))$ is the observed data
and a sample consists of $O = (O_1, dots, O_n)$ for $n$ independent and identically distributed observations
with $O_i tilde P$.
We will formally show @eq:ftkcens later.

Define $cumhazardcensored(k, c, dif t)$ as the cause-specific cumulative hazard measure of the $k$'th event and that the event was a censoring event at time $t$ given the observed history $historycensored(k-1)$
and define the corresponding censoring survival function $tilde(S)^c (t | historycensored(k-1)) = prodint(s, event(k-1), t) (1 - cumhazardcensored(k, c, dif s))$.
This determines the probability of being observed at time $t$ given the observed history
up to $historycensored(k-1)$.

= Algorithm for ICE-IPCW Estimator <alg:ipcwice>

In this section, we present an algorithm for the ICE-IPCW estimator and consider its use in a simple data example.

//(note that this approach is valid as a consequence of @thm:ice is that $cumhazard(k, x, dif t)$ for $x = a, ell, d, y$ are identified via the observed data).

It requires as inputs the dataset $cal(D)_n$, a time point $tau$ of interest, and a cause-specific cumulative hazard model $cal(L)_h$​ for the censoring process.
This model takes as input the event times, the cause of interest, and covariates from some covariate space $bb(X)$,
and outputs an estimate of the cumulative cause-specific hazard function $hat(Lambda)^c: (0, tau) times bb(X) -> RR_+$ for the censoring process.
It is technically allowed for this procedure to only give estimates
of $1/(P(eventcensored(k) >= t | historycensored(k-1))) P(eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1))$, which is always estimable from observed data, and not $1/(P(C >= t | historycensored(k-1))) P(C in dif t | historycensored(k-1))$.
For all practical purposes, we will assume that these are the same. 

The algorithm also takes a model $cal(L)_o$ for the iterative regressions, which returns a prediction function $hat(nu): bb(X) -> RR_+$ for the pseudo-outcome.
Ideally, both models should be chosen flexibly, since even with full knowledge of the data-generating mechanism, the true functional form of the regression model
cannot typically be derived in closed form.
Also, the model should be chosen such that the predictions are $[0,1]$-valued.

For use of the algorithm in practice, we shall choose $K$ such that $K=max_(i in {1, dots, n}) K_i (tau)$,
where $K_i (tau)$ is the number of non-terminal events for individual $i$ in the sample.
However, we note that this may not always be possible as there might be few people with many events.
Therefore, one may have to prespecify $K$ instead
and define a composite outcome. Specifically, we let
$k^* = inf {k in {K+1, dots, max_i K_i (tau)} | statuscensored(k) in {y, d, c}}$,
and $macron(T)^*_((K+1)) = eventcensored(k^*)$ and $macron(D)^*_((K+1)) = statuscensored(k^*)$
and use the data set where $eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k)$ for $k > K+1, dots, k^*$
are removed from the data and instead $macron(T)^*_((K+1))$ and $macron(D)^*_((K+1))$ are used as the event time and status for the $(K+1)$'th event.
Strictly speaking, we are not estimating the interventional cumulative incidence function at time $tau$
as we set out to do originally because the intervention has changed.
In this situation, the doctor will only have to prescribe treatment to patients who visit the doctor
as part of their $k^*$ first events. However, this estimand is likely to be close to the original estimand
of interest.
The algorithm can then be stated as follows:

- For each event point $k = K+1, K, dots, 1$ (starting with $k = K$):
    1. Regress $macron(S)_((k)) = eventcensored(k) - eventcensored(k-1)$, known as the $k$'th _interarrival_ time,
       with the censoring as the cause of interest
       on $historycensored(k-1)$ (among the people who are still at risk after $k-1$ events,
       that is $R_k = {i in {1, dots, n} | macron(Delta)_(k-1,i) in {a, ell}}$ if $k > 1$ and otherwise $R_1 = {1, dots, n}$)
       using $cal(L)_h$
       to obtain an estimate of the cause-specific cumulative hazard function $hat(Lambda)_k^c$.
       For $k=1$, note that we take $eventcensored(0) = 0$.
    2. Obtain estimates $hat(S)^c (eventcensored(k)- | historycensored(k-1)) = 
    product_(s in (0, macron(T)_(k+1)-macron(T)_(k))) (1 - hat(Lambda)_k^c (s | historycensored(k-1)))$ from step 1.
    3. Calculate the subject-specific pseudo-outcome:
       $
           hat(m)_k = (bb(1) {eventcensored(k) <= tau, statuscensored(k) = y}) / (hat(S)^c (eventcensored(k) - | historycensored(k-1))) \
       $
       Then,
       - If $k <= K$:
       
       Let $cal(F)^g_(eventcensored(k))$ denote the history with
       $treatcensored(k) = 1$ if $statuscensored(k) = a$. Otherwise, $cal(F)^g_(eventcensored(k)) = historycensored(k)$.
       Then calculate, 
       $
           hat(Z)^a_k = (bb(1) {eventcensored(k) < tau, statuscensored(k) in {a, ell}} hat(nu)_(k) (cal(F)^g_(eventcensored(k)))) / (hat(S)^c (eventcensored(k)- | historycensored(k-1))) + hat(m)_k.
       $
       - If $k = K + 1$, put
       $
           hat(Z)^a_k = hat(m)_k.
       $
    4. Regress $hat(Z)^a_k$ on $historycensored(k-1)$ with model $cal(L)_o$ on the data with $eventcensored(k-1) < tau$ and $statuscensored(k-1) in {a, ell}$ to obtain a prediction function $hat(nu)_(k-1) : cal(H)_(k-1) -> RR^+$.
       Here we denote by $cal(H)_(k-1)$ the set of possible histories of the process up to and including the $k-1$'th event.
       //where $historycensored(k-1) in cal(H)_(k-1)$.
           
- At baseline, we obtain the estimate $hat(Psi)_n = 1/n sum_(i=1)^n hat(nu)_(0) (1, L_i (0))$.

Note that the third step, we can alternatively in $cal(F)^g_(eventcensored(k))$
replace all prior treatment values with 1,
that is $treat(0) = dots = treatcensored(k-1) = 1$. This is certainly closer
to the iterative conditional expectation estimator as proposed by @bangandrobins2005, but is mathematically equivalent
as we, in the next iterations, condition on the treatment being set to 1.
This follows from standard properties of the conditional expectation (see e.g., Theorem A3.13 of @last1995marked).

In the first step, the modeler wish to alter the history from an intuitive point of view, so that, in
the history $historycensored(k-1)$, we use the variables $macron(T)_(k-1) - macron(T)_(j)$ for $j <= k-1$
instead of the variables $macron(T)_(j)$,
altering the event times in the history to "time since last event" instead of the "event times" 
(note that we should then remove $macron(T)_(k-1)$ from the history as it is identically zero).
This makes our regression procedure in step 1 intuitively look like a simple regression procedure at time zero.

We also need to discuss what models should be used for $Qbar(k)$.
Note that 
$
    bb(1) {event(k) < tau and status(k) in {a,ell}} Qbar(k) =  mean(P^(G^*)) [N^y (tau)  | history(k)] bb(1) {event(k) < tau and status(k) in {a,ell}} 
$
We see thus see that we should use a model for $Qbar(k)$ that is able to capture the counterfactual probability of the primary event occuring at or before time $tau$
given the history up to and including the $k$'th event (among the people who are at risk of the event before time $tau$ after $k$ events).
//Looking at the algorithm, we see that this does not matter as no observations; indicator functions are all zero.
// otherwise we would not have data.

// e.g., E[ h(X, Y) | Y=1] = E[ h(X, 1) | Y=1]

== Example usage of the Algorithm <section:example>

To help illustrate the algorithm, we present a simple example in @fig:longitudinaldataice in the case where $tau = 5$.
Since $K=2$ in @fig:longitudinaldataice, we start at $k=3$.

#outline-colorbox(
      title: [Iteration $k=3$],
        color: "blue",
        radius: 2pt,
    width: auto,
    centering: true,
          )[
 1. First, we fit a cause-specific hazard model for people at risk of the $k$'th event, $R_3$. We find that $R_3 = {3, 4, 7}$.
    Here, the interarrival times are given by 
    $macron(S)_((3),3) = 5-2.1=2.9, macron(S)_((3),4) = 8 - 6.7 = 1.3, macron(S)_((3),7) = 4.9-4.7 = 0.2$, and status indicators $macron(Delta)_(3,3)^c = 0$, $macron(Delta)_(3,4)^c = 0$, $macron(Delta)_(3,7)^c = 1$ respectively.
    Let $cal(F)^(tilde(beta))_(macron(T)_(2,i))= (L_i (0), A_i (0), L_i (macron(T)_(1,i)), A_i (macron(T)_(1,i)), macron(T)_(1,i), macron(Delta)_(1,i), L_i (macron(T)_(2,i)), A_i (macron(T)_(2,i)), macron(T)_(2,i), macron(Delta)_(2,i))$.
    To obtain $hat(Lambda)^c$, we regress the event times $macron(S)_(3)$ on $cal(F)^(tilde(beta))_(macron(T)_(2))$ with status indicator $macron(Delta)_3^c$.
              
2/3. From $hat(Lambda)^c$ obtain estimates $hat(S^c) (macron(T)_(3,i)- | cal(F)^beta_(macron(T)_(2,i)))$ for $i in R_3 inter {i : macron(T)_(2,i) < tau} = {3,7}$.
     We assume that these are given by $hat(S^c) (macron(T)_(3,3)- | cal(F)^beta_(macron(T)_(2,3))) = 0.8$, $hat(S^c) (macron(T)_(3,7)- | cal(F)^beta_(macron(T)_(2,7))) = 0.9$.
     Then, we calculate $hat(Z)_(3,3)^a = (bb(1) {macron(T)_(3,3) <= tau, macron(Delta)_(3,3) = y}) / (hat(S^c) (macron(T)_(3,3)- | cal(F)^beta_(macron(T)_(2,3)))) = 1/0.8 = 1.25$,
     $hat(Z)_(3,7)^a = (bb(1) {macron(T)_(3,7) <= tau, macron(Delta)_(3,7) = y}) / (hat(S^c) (macron(T)_(3,7)- | cal(F)^beta_(macron(T)_(2,7)))) = 0/0.9 = 0$.
4. Regress the predicted values $hat(Z)^a_(3)$ on $historycensored(2)$ to obtain a prediction function $hat(nu)_(2)$.
        
          ]
#outline-colorbox(
        title: [Iteration $k=2$],
          color: "blue",
          radius: 2pt,
            width: auto,
            centering: true,
            )[

1. As in the case $k=3$, we fit a cause-specific hazard model for people at risk of the $k$'th event, $R_2$.
   We find that $R_2 = {1, 3, 4, 6, 7}$.
   Here, the interarrival times are given by $macron(S)_((2),1) = 8-0.5=7.5$, $macron(S)_((2),3) = 2.1-2=0.1$, $macron(S)_((2),4) = 6.7-6=0.7$, $macron(S)_((2),6) = 5-1=4$, $macron(S)_((2),7) = 4.7-4=0.7$,
   and $macron(Delta)_(2,i)^c = 0$ for $i = 1, 3, 4, 6, 7$. Regress the event times $macron(S)_(2)$ on $cal(F)^(tilde(beta))_(macron(T)_(1))$ with status indicators $macron(Delta)_2^c$
   to obtain $hat(Lambda)^c$.
2/3. From $hat(Lambda)^c$ obtain estimates $hat(S^c) (macron(T)_(2,i)- | cal(F)^beta_(macron(T)_(1,i)))$ for $i in R_2 inter {i : macron(T)_(1,i) < tau} = {1, 3, 6, 7}$.
We assume that these are given by $hat(S^c) (macron(T)_(2,1)- | cal(F)^beta_(macron(T)_(1,1))) = 0.9$, $hat(S^c) (macron(T)_(2,3)- | cal(F)^beta_(macron(T)_(1,3))) = 0.8$, $hat(S^c) (macron(T)_(2,6)- | cal(F)^beta_(macron(T)_(1,6))) = 0.7$, $hat(S^c) (macron(T)_(2,7)- | cal(F)^beta_(macron(T)_(1,7))) = 0.6$.
Then, we calculate $hat(Z)_(2,1)^a = 0/0.9 = 0, hat(Z)_(2,6) = 0/0.7 = 0$. We now apply the prediction functions from step $k=3$.
  - For $i=3$, we produce the altered history, where $cal(F)^g_(macron(T)_(2,i)) = (3,1, 4,1, 2, ell, 4, 1, 2.1, a)$
    and apply $hat(nu)_2 (cal(F)^g_(macron(T)_(2,3))) = 0.3$,
    so we get $hat(Z)^a_(2,i) = (bb(1) {macron(T)_(2,i) < tau, macron(Delta)_(2,i) in {a, ell}} hat(nu)_(2) (cal(F)^g_(macron(T)_(2,i)))) / (hat(S^c) (macron(T)_(2,i)- | cal(F)^beta_(macron(T)_(1,i)))) = 0.3/0.8 = 0.375$.
  - For $i = 7$, we keep the history and get $hat(nu)_2 (cal(F)^g_(macron(T)_(2,7))) = 0.25$, so
    we get $hat(Z)_(2,3)^a = (bb(1) {macron(T)_(2,3) < tau, macron(Delta)_(2,3) = a}) / (hat(S^c) (macron(T)_(2,3)- | cal(F)^beta_(macron(T)_(1,3)))) hat(nu)_(2)(cal(F)^g_(macron(T)_(1,3))) = 0.25/0.8 = 0.3125$.
4. Regress the predicted values $hat(Z)^a_(2)$ on $historycensored(1)$ to obtain a prediction function $hat(nu)_(1)$.
            ]
#outline-colorbox(
        title: [Iteration $k=1$],
          color: "blue",
          radius: 2pt,
            width: auto,
            centering: true,
            )[

Same procedure as $k=2$. Note that the interarrival times are simply given by the event times here.
            ]
#outline-colorbox(
        title: [Iteration $k=0$],
          color: "blue",
          radius: 2pt,
            width: auto,
            centering: true,
            )[

We get the estimate $hat(Psi)_n = 1/7 sum_(i=1)^7 hat(nu)_(0) (1, L_i (0))$ for $n=7$,
where we obtained $hat(nu)_(0)$ from $k=1$.
            ]

#figure(table(
    columns: (auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto),
                inset: 10pt,
            align: horizon,
    table.header(
        [id], [$covariate(0)$], [$treat(0)$], 
        [$covariatecensored(1)$], [$treatcensored(1)$], [$eventcensored(1)$], [$statuscensored(1)$],
        [$covariatecensored(2)$], [$treatcensored(2)$], [$eventcensored(2)$], [$statuscensored(2)$],
        [$eventcensored(3)$], [$statuscensored(3)$]
    ),
    [1], [2], [1], [2], [1], [0.5], [$a$], [Ø], [Ø], [8], [$y$], [$oo$], [Ø],
    [2], [1], [0], [Ø], [Ø], [10], [$y$], [Ø], [Ø], [$oo$], [Ø], [$oo$], [Ø],
    [3], [3], [1], [4], [1], [2], [$ell$], [4], [0], [2.1], [$a$], [$5$], [$y$],
    [4], [3], [1], [4], [1], [6], [$ell$], [4], [0], [6.7], [$a$], [$8$], [$y$],
    [5], [1], [1], [Ø], [Ø], [3], [$d$], [Ø], [Ø], [$oo$], [Ø], [$oo$], [Ø],
    [6], [1], [1], [0], [3], [1], [$ell$], [Ø], [Ø], [5], [$d$], [Ø], [Ø],
    [7], [3], [1], [4], [1], [4], [$ell$], [5], [1], [4.7], [$ell$], [$4.9$], [$c$],

                ),
                caption: [
                    Example data for illustration of the ICE-IPCW algorithm. 
                ])<fig:longitudinaldataice>

= Consistency of the ICE-IPCW Estimator <section:conditions>

Now let $N^c (t) = bb(1) {C <= t}$ the counting process for the censoring process and
let $T^e$ further denote the (uncensored) terminal event time given by
$
    T^e = inf_(t>0) {N^y (t) + N^d (t) = 1}.
$
and let $beta(t) = (alpha(t), N^c (t))$ be the fully observable multivariate jump process in $[0, tauend]$.
We assume now that we are working in the canonical setting with $beta$ and not $alpha$.

// We have in the canonical setting with $beta$
// that also #footnote[This follows by considering the sub $sigma$-algebra corresponding to $((event(k),status(k),treat(k),covariate(k)))_(k=1)^K$
//     and $P$'s restriction to that sub $sigma$-algebra, because we are then in the canonical setting for $N^alpha$.]
// $
//     history(k) = sigma(event(k), status(k), treat(k), covariate(k), dots, event(1), status(1), treat(1), covariate(1), treat(0), covariate(0))
// $

// $
//     N^alpha ((0,t] times {x} times dot times dot) &= bb(1) {x in {a, ell, d, y}} N^alpha ((0, t] times {x} times dot times dot) + bb(1) {x = c} N^c (t) delta_((A(C), L(C))) (dot times dot).
// $
//= cal(F)_(t and C) or cal(G)_(t and T^e),$ 
//where $cal(G)_t = sigma(N^c (s) | s <= t)$ denotes the filtration generated by the censoring process.
//(for a stopping time $T>0$, we use $cal(F)_(t and T)$ to denote stopping time $sigma$-algebra given by the stopping time $t and T$.).

Then, we observe the trajectories of the process given by $t mapsto N^beta (t and C and T^e)$
and the observed filtration is given by 
$cal(F)_t^tilde(beta) = sigma(beta(s and C and T^e) | s <= t)$.
The observed data is then given by @eq:observedata.
Importantly, we have in fact #footnote[The fact that the stopped filtration and the filtration generated by the stopped process are the same is not obvious but follows by Theorem 2.2.14 of @last1995marked.
Moreover, from this we have $historycensored(k) = cal(F)^(beta)_(event(k) and C and T^e)$ and we may apply Theorem 2.1.14 to the right-hand side of $cal(F)^(beta)_(event(k) and C and T^e)$ to get the desired statement. ].
$
    historycensored(k) = sigma(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k), dots, eventcensored(1), statuscensored(1), treatcensored(1), covariatecensored(1), treat(0), covariate(0)).
$
Abusing notation a bit, we see that for observed histories, we
have $history(k) = historycensored(k)$ if $statuscensored(k) != c$.
Note that here we also have not shown that $history(k) = sigma( event(k), status(k), treat(k), covariate(k), dots, event(1), status(1), treat(1), covariate(1), treat(0), covariate(0))$.
However, our results up to this point only rely on conditioning on the variables representing the history up to and including the $k$'th event.
// Also note that the stopping time sigma algebra for alpha can remain the same; we did not use that it was a stopping time sigma algebra in the previous sections; only
// the fact that it is a sigma algebra generated by the observations up to the $k$'th event. 

In this section, we present the conditions under which the ICE-IPCW estimator is consistent for the target parameter.
What we require for the identification via the iterated regressions, is that 
$
    &P(event(k) in [t, t + dif t), status(k) = x, treat(k) = m, covariate(k) = l | history(k-1), event(k) >= t) \
        &= P(eventcensored(k) in [t, t + dif t), statuscensored(k) = x, treatcensored(k) = m, covariatecensored(k) = l | historycensored(k-1), eventcensored(k) >= t), qquad x!= c.
$ <eq:indep>
// Flemming and Harrington; generalization of Theorem 1.3.2.
// to be proven when I feel like it.
for uncensored histories, i.e., when $statuscensored(k-1) != c$ as well as regularity condition 1 and 2 in @thm:ice.

We posit specific conditions in @thm:ice similar to those that may be found the literature based on independent censoring (@andersenStatisticalModelsBased1993; Definition III.2.1)
or local independence conditions (@roeysland2024; Definition 4).
Alternatively, we may assume coarsening at random which will imply @eq:indep (e.g., @gill1997coarsening).

//I@thm:ice
//This is essentially the weakest condition such that the observed data martingales
//actually identify the unobserved hazards and probabilities.

#theorem[
    Assume that the compensator $Lambda^alpha$ of $N^alpha$ with respect to the filtration $cal(F)^beta_t$ is
    also the compensator with respect to the filtration $cal(F)_t$.
    Then for uncensored histories, we have 
    $
        &bb(1) {statuscensored(n-1) != c} P ((macron(T)_(n), macron(Delta)_(n), A(macron(T)_(n)), L(macron(T)_(n))) in d (t, m, a,l)| historycensored(n-1)) \
            &= bb(1) {macron(T)_(n-1) < t,statuscensored(n-1) != c} (tilde(S) (t- | historycensored(n-1)) sum_(x=a,ell,d,y) delta_x (dif m) psi_(n,x) (t, d(a, l)) cumhazard(n, x, dif t) \
                &qquad + delta_((c, treat(n-1), covariate(n-1))) (dif (m, a, l)) cumhazardcensored(n, c, dif t)) \
    $ <eq:densitycens>
    where
    $
        psi_(n, x) (t, history(n-1),dif (m, a, l)) &=   bb(1) {x = a}(delta_(1) (dif a) densitytrt(t, n) + delta_(0) (dif a) (1 - densitytrt(t, n))) delta_(covariate(n-1)) (dif l) \
            &+ bb(1) {x = ell} densitycov(d l, t, n) delta_(treat(n-1)) (dif a) \
            &+ bb(1) {x in {y, d}} delta_(treat(n-1)) (dif a) delta_(covariate(n-1)) (dif l).
    $ <eq:mark>
    and $bb(1) {statuscensored(n-1) != c} tilde(S) (t | historycensored(n-1)) = bb(1) {statuscensored(n-1) != c} product_(s in (event(k-1),t]) (1 - sum_(x=a,ell,y,d) cumhazard(n, x, dif s) - cumhazardcensored(n, c, dif s))$.
    
    Further supposee that:
    1. $bb(1) {statuscensored(n-1) != c} tilde(S) (t | historycensored(n-1)) = bb(1) {statuscensored(n-1) != c} tilde(S)^c (t | historycensored(n-1)) S (t | history(n-1))$.
    2. $tilde(S)^c (t | historycensored(n-1)) > eta$ for all $t in (0, tau]$ and $n in {1, dots, K}$ $P$-a.s. for some $eta > 0$.
    Then, the ICE-IPCW estimator is consistent for the target parameter, i.e.,
    #math.equation(block: true, numbering: "(1)")[$
        bb(1) {statuscensored(k-1) != c} Qbar(k-1) &= bb(1) {statuscensored(k-1) != c} mean(P) [(bb(1) {eventcensored(k) < tau, statuscensored(k) = ell})/( tilde(S)^c (eventcensored(k-1) - | historycensored(k-1)) ) Qbar(k)(treatcensored(k-1), covariatecensored(k), eventcensored(k), statuscensored(k), historycensored(k-1)) \
            &#h(1.5cm) + (bb(1) {eventcensored(k) < tau, statuscensored(k) = a}) /(tilde(S)^c (eventcensored(k-1) - | historycensored(k-1)))  Qbar(k) (1, covariatecensored(k-1), eventcensored(k), statuscensored(k), historycensored(k-1)) \
            &#h(1.5cm) + (bb(1) {eventcensored(k) <= tau, statuscensored(k) = y}) /(tilde(S)^c (eventcensored(k-1) - | historycensored(k-1))) mid(|) historycensored(k-1)]
    $] <eq:ipcw>
    for $k = K, dots, 1$ and
    $
        Psi_tau^g (P) = mean(P) [  Qbar(0) (1, covariate(0))].
    $<eq:ice2>
] <thm:ice>
#proof[
    Under the local independence condition, a version of the compensator of the random measure $N^alpha (dif (t, m, a, l))$ with respect to the filtration $cal(F)^beta_t$,
    can be given by Theorem 4.2.2 (ii) of @last1995marked,
    $
        Lambda^alpha (dif (t, m, a, l)) &= K'((L(0), A(0)), N^alpha, t, dif (m, a, l)) V' ((A(0),L(0)), N^alpha, dif t)
    $ <eq:ff>
    for some kernel $K'$ from ${0, 1} times cal(L) times N_bold(X) times RR_+$ to $RR_+ times bold(X)$
    and some predictable kernel $V'$ from ${0, 1} times cal(L) times N_bold(X) times RR_+$ to $RR_+ times bold(X)$,
    because the _canonical_ compensator is uniquely determined (so we first find the canonical compensator for the smaller filtration $cal(F)^alpha_t$
    and then conclude that it must also be the canonical compensator for the larger filtration $cal(F)^beta_t$).
    // Øjensynligt er denne kompensator integrabel og adapted til den større filtration. Tillige er den forudsigelig.
    // Den relevante MG condition er også opfyldt da kompensator er indistinguishable, og derfor er tilde M_t = M_t n.s. og dermed conditional expectations ens.
    
    Similarly, we can find a compensator of the process $N^c (t)$ with respect to the filtration $cal(F)^beta_t$ given by
    $
        Lambda^c (dif t) &= K'((L(0), A(0)), N^beta, t, dif (m, a, l)) V' ((A(0),L(0)), N^beta, dif t) 
    $
    for some kernel $K''$ from ${0, 1} times cal(L) times N_bold(X) times RR_+$ to $RR_+ times bold(X)$.
    We now find the _canonical_ compensator of $N^beta$, given by
    $
        rho ((l_0, a_0), phi^beta, d (t, m, a, l)) &= bb(1) {m in {a, ell, d, y}} K'((l_(0), a_(0)), phi^alpha, t, dif (m, a, l)) V' ((a_(0),l_(0)), phi^alpha, dif t) \
            &+ K''((l_(0), a_(0)), phi^beta, t) V' ((a_(0),l_(0)), phi^beta, dif t) delta_((c, A(C), L(C))) (dif (m, a, l)).
    $
    Then $rho ((covariate(0),treat(0)), N^(beta), d (t, m, a, l))$ is a compensator,
    so it is by definition the canonical compensator.
    In view of Theorem 4.3.8 of @last1995marked,
    $
        K''((l_(0), a_(0)), cal(F)_eventcensored(n-1), t) V' ((a_(0),l_(0)), cal(F)_eventcensored(n-1), (0, t]) = tilde(Lambda)_n^c (t | historycensored(n-1)).
    $
    and similarly, we see that
    $
        K'((l_(0), a_(0)), cal(F)_eventcensored(n-1), t, dif (m, a, l)) V' ((a_(0),l_(0)), cal(F)_eventcensored(n-1), dif (t, m, a, l)) = sum_(x=a,ell,d,y) psi_(n,x) (t, d(a,l), history(n-1)) Lambda_n^x ((0, t] | history(n-1))
    $
    // Do we need to show whether Delta Rho <= 1?

    Let $T_((k))^*$ denote the ordered event times of the process $N^beta$.
    With $S:= T^e and C and event(k)$, we
    have $T_(S,0) = T^e and C and event(k) = eventcensored(k)$.
    Using Theorem 4.3.8 of @last1995marked, it therefore holds that
    $
        &P( (T_(S,1)^*, Delta_(S,1)^*, A(T_(S,1)^*), L(T_(S,1)^*)) in d (t, m, a,l) | cal(F)^(tilde(beta))_(eventcensored(k)))\
        &=P( (T_(S,1)^*, Delta_(S,1)^*, A(T_(S,1)^*), L(T_(S,1)^*)) in d (t, m, a,l) | cal(F)^(beta)_(T_(S,0))) \
            &= bb(1) {T_(S,0) < t} product_(s in (T_(S,0), t)) (1 - rho ((L(0),A(0)), cal(F)^(beta)_(T_(S,0)), d s, {a,y,l,d,y} times {0,1} times cal(L))) rho ((L(0),A(0)), cal(F)^(tilde(beta))_(T_(S,0)), d (t, m, a, l)) \
            &= bb(1) {eventcensored(k-1) < t} product_(s in (T_(S,0), t)) (1 - rho ((L(0),A(0)), cal(F)^(tilde(beta))_(eventcensored(k)), d s, {a,y,l,d,y} times {0,1} times cal(L))) rho (A(0), L(0), cal(F)^(tilde(beta))_(eventcensored(k)), d (t, m, a, l)).
    $
    Further note that $T^*_k = eventcensored(k)$ whenever $event(k-1) < C$. By definition, $T_(S,1) = T^*_(k+1)$ if $N^beta (event(k) and C and T^e) = k$.
    If $statuscensored(1) in.not {c,y,d},dots ,statuscensored(k) in.not {c,y,d}$, then $N^beta (event(k) and C and T^e) = k$ and furthermore $T^*_(k+1) = eventcensored(k+1)$, so
    $
        &bb(1) {statuscensored(1) in.not{c,y,d}, dots, statuscensored(k) in.not {c,y,d}} P( (macron(T)_(k+1), macron(Delta)_(k+1), A(macron(T)_(k+1)), L(macron(T)_(k+1))) in d (t, m, a,l) | cal(F)^(tilde(beta))_(eventcensored(k)))\
            &=bb(1) {statuscensored(1) in.not {c,y,d}, dots, statuscensored(k) in.not {c,y,d}} P( (T_(S,1)^*, Delta_(S,1)^*, A(T_(S,1)^*), L(T_(S,1)^*)) in d (t, m, a,l) | cal(F)^(tilde(beta))_(eventcensored(k)))\
            &=bb(1) {statuscensored(1) in.not {c,y,d}, dots, statuscensored(k) in.not {c,y,d}} bb(1) {eventcensored(k-1) < t} \
            &qquad product_(s in (T_(S,0), t)) (1 - rho ((L(0),A(0)), cal(F)^(tilde(beta))_(eventcensored(k)), d s, {a,y,l,d,y} times {0,1} times cal(L))) rho (A(0), L(0), cal(F)^(tilde(beta))_(eventcensored(k)), d (t, m, a, l)).
    $
    and we are done.
    From this, we get @eq:densitycens.
    Applying this to the right hand side of @eq:ipcw
    shows that it is equal to @eq:iterative.    
]

Note that @eq:densitycens also ensures that all hazards (other than censoring) and mark probabilities are identifiable from censored data
if we can show that the censoring survival factorizes.
We provide two criteria for this.
The stated conditional independence condition in @thm:condindcens is likely
much stronger than we need for identification, but is overall simple.
@thm:survivalfactorgeneral also gives a criterion, but is more generally stated.
A simple consequence of the second is that if compensator of the (observed) censoring
process is absolutely continuous with respect to the Lebesgue measure,
then the survival function factorizes.

#theorem[
    Assume that for each $k = 1,dots, K$,
    $
        (event(k),status(k),treat(k),covariate(k)) perp C | history(k-1)
    $
    Then the survival function factorizes
    $
        bb(1) {statuscensored(k) !=c} tilde(S) (t | historycensored(k)) = bb(1) {statuscensored(k) !=c}product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) cumhazard(k, x, dif s)) product_(s in (0, t]) (1 - tilde(Lambda)_k^c (dif t | historycensored(k-1)))
    $
    and the local independence statement given in @eq:densitycens holds.
] <thm:condindcens>

#proof[
    We first show the local independence statement $tilde(cal(F))^beta = sigma(alpha(s) | s <= t) or cal(Z)_0$, where $cal(Z)_0 = sigma(treat(0), covariate(0), C)$.
    Evidently, $cal(F)_t subset.eq cal(F)^beta_t subset.eq tilde(cal(F))^beta_t$.
    Under the independence assumption, by the use of the canonical compensator,
    the compensator for $N^alpha$ for $cal(F)_t$ is also the compensator for $tilde(cal(F))^beta_t$.
    Let $M^alpha$ denotes the corresponding martingale decomposition (since $mean(P) [N_t] <= K < oo$, we may work with martingales instead of _local_ martingales). It follows that
    $
        &mean(P) [M^alpha ((0,t] times dot times dot times dot) | cal(F)^beta_s] \
            &=^"(i)" mean(P) [mean(P) [M^alpha ((0,t] times dot times dot times dot) | tilde(cal(F))^beta_s]| cal(F)^beta_s] \
            &=^"(ii)" mean(P) [M^alpha ((0,s] times dot times dot times dot) | cal(F)^beta_s] \
            &=^"(iii)" M^alpha ((0,s] times dot times dot times dot) \
    $
    which implies the desired statement. In part (i), we use the law of iterated expectations, in part (ii), we use that the martingale is a martingale for $tilde(cal(F))^beta_t$.
    In part (iii), we use that the martingale is $cal(F)_t^alpha$-adapted.
    This shows the desired local independence statement.

    By the stated independence condition, it follows immediately that
    $
        bb(1) {statuscensored(k) !=c} tilde(S) (t | history(k)) &=bb(1) {statuscensored(k) !=c} P(min{event(k),C} > t| history(k)) \
            &=bb(1) {statuscensored(k) !=c} P(event(k) > t, C > t| history(k)) \
            &= bb(1) {statuscensored(k) !=c}S(t | history(k)) S^c (t | history(k)).
    $
    By the first part of @thm:ice, we have that
    $
        bb(1) {statuscensored(k) !=c} tilde(S) (t | historycensored(k))  &= bb(1) {statuscensored(k) !=c} product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) cumhazard(k, x, dif s) - tilde(Lambda)_k^c (dif s | historycensored(k-1))) \
    $
    and we have that
    $
        S (t | history(k)) &= product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) cumhazard(k, x, dif s)),
    $
    so it follows that we just need to show that
    $
        bb(1) {statuscensored(k) !=c} product_(s in (0, t]) (1 - Lambda_k^c (dif s | historycensored(k-1))) = bb(1) {statuscensored(k) !=c} product_(s in (0, t]) (1 - tilde(Lambda)_k^c (dif s | historycensored(k-1)))
    $
    Because of the independence condition (using, for instance, Tonelli's theorem ???), we have that
    $
        P (eventcensored(k) <= t, statuscensored(k) = c | history(k-1)) = P (C <= t, C > event(k) | history(k-1)) = integral_((0,t]) S (s- | history(k-1)) S^c (s- | history(k-1)) Lambda_k^c (dif s | history(k-1))
    $ <eq:densitycens2>
    and thus
    $
        tilde(Lambda)_k^c (dif t | history(k-1)) &= (P (eventcensored(k) in dif t, statuscensored(k) = c | history(k-1))) / (S (t- |history(k-1)) S^c (t- | history(k-1))) = Lambda_k^c (dif t | history(k-1)) \
    $
    where 
    $
        S^c (t | history(k-1)) &= product_(s in (0, t]) (1 - Lambda_k^c (dif s | history(k-1))).
    $
]

#theorem[
    Assume independent censoring as in @thm:ice.
    Then the left limit of the survival function factorizes on $(0, tau]$, i.e.,
    $
        bb(1) {statuscensored(k-1)!=c} tilde(S) (t- | history(k-1)) &= bb(1) {statuscensored(k-1)!=c}product_(s in (0, t)) (1 - sum_(x=a,ell,y,d) cumhazard(k, x, dif s)) product_(s in (0, t]) (1 - tilde(Lambda)_k^c (dif t | historycensored(k-1)))
    $ 
    if for all $t in (0, tau)$,
    $
        Delta tilde(Lambda)_(k)^c (t | historycensored(k-1)) + sum_x Delta cumhazard(k, x, t) = 1 quad P-"a.s."=> Delta tilde(Lambda)_(k+1)^c (t | history(k-1)) = 1 quad P-"a.s." or sum_x Delta cumhazard(k, x, t) = 1 quad P-"a.s."
    $ //i.e., there is exists only convex combination of the two terms that can be 1.
] <thm:survivalfactorgeneral>
// Can we derive the fi-di result directly from the likelihood; because then it factorizes.
#proof[
    First, we argue that for every $t in (0, tau]$ with $tilde(S) (t- | historycensored(k-1)) > 0$ (so dependent on the history), we have
    //@eq:tildeSfactor.
    To show this, consider the quadratic covariation process which by the no simultaneous jump condition implies is zero, and thus
    $
        0=[M^c (dot and T^e),sum_x M^x (dot and C)]_t = integral_0^t Delta tilde(Lambda)_c sum_(x=a,ell,y,d) d Lambda_x
    $
    where $tilde(Lambda)_c$ and $Lambda_x$ are the compensators of the censoring process and the rest of the counting processes, respectively.
Using this, we have
$
    0 &= sum_(k=1)^K bb(1) {event(k-1) and C< t <= event(k) and C} (integral_((event(k-1) and C, t]) Delta cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) cumhazard(k, x, dif s)) \
        &qquad + sum_(j=1)^(k-1) integral_((event(j-1) and C, event(j) and C]) Delta tilde(Lambda)_c (s | historycensored(j-1)) (sum_(x=a,ell,y,d) cumhazard(k, x, dif s)))
$
so that $bb(1) {event(k-1) and C < t <= event(k) and C} integral_((event(k-1), t]) Delta cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) cumhazard(k, x, dif s)) = 0$.
    Taking the (conditional) expectations on both sides, we have
    $
        bb(1) {event(k-1) and C < t} tilde(S) (t- | historycensored(k-1)) sum_(eventcensored(k) < s <= t) Delta cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) Delta cumhazard(k, x, s)) &= 0,
    $ <eq:condProof>
    where we also use that $Delta cumhazardcensored(k, c, s) != 0$ for only a countable number of $s$'s.
    This already means that the continuous part of the Lebesgue-Steltjes integral is zero, and thus the integral is evaluated to the sum in @eq:condProof.
    It follows that for every $t$ with $tilde(S) (t- | cal(F)^tilde(beta)_(macron(T)_k)) > 0$,
    $
        sum_(macron(T)_(k) < s <= t) Delta cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) Delta cumhazard(k, x, s)) &= 0.
    $
    This entails that $Delta tilde(Lambda)_(k+1)^c (t | historycensored(k-1))$ and $sum_x Delta cumhazard(k+1, x, t)$ cannot be both non-zero at the same time.
    To keep notation brief, let $gamma = Delta tilde(Lambda)_(k+1)^c (t | historycensored(k-1))$ and $zeta = sum_x Delta cumhazard(k+1, x, t)$
    and $s = macron(T)_(k-1)$.
    
    Then, we have shown that
    $
        bb(1) {product_(v in (s, t)) (1 - d (zeta+gamma)) > 0} product_(v in (s, t)) (1 - d (zeta+gamma)) = bb(1) {product_(v in (s, t)) (1 - d (zeta+gamma)) > 0} product_(v in (s, t)) (1 - zeta) product_(v in (s, t]) (1 - gamma)
    $
    since
    $
        product_(v in (s, t)) (1 - d (zeta+gamma)) &= exp(-beta^c) exp( -gamma^c) product_(v in (s, t) \ gamma(v) != gamma(v-) or zeta(v) != zeta(v-))  (1 - Delta ( zeta+gamma)) \
            &= exp(-beta^c) exp( -gamma^c) product_(v in (s, t) \ gamma(v) != gamma(v-)) (1- Delta gamma) product_(v in (s, t) \ zeta(v) != zeta(v-)) (1 - Delta zeta) \
            &= product_(v in (s, t)) (1 - zeta) product_(v in (s, t)) (1 - gamma)
    $
    under the assumption $product_(v in (s, t)) (1 - d (zeta+gamma))>0$.
    So we just need to make sure that $product_(v in (s, t)) (1 - d (zeta+gamma) = 0$ if and only if $ product_(v in (s, t)) (1 - zeta) = 0$ or $product_(v in (s, t)) (1 - gamma) = 0$.
    Splitting the product integral into the continuous and discrete parts as before, we have
    $
        product_(v in (s, t)) (1 - d (zeta+gamma)) = 0 <=> exists u in (s, t) "s.t." Delta gamma (u) + Delta zeta (u) = 1 \
        product_(v in (s, t)) (1 - d gamma) product_(v in (s, t)) (1-zeta) = 0 <=> exists u in (s, t) "s.t." Delta gamma (u) = 1 or exists u in (s, t) "s.t." Delta zeta (u) = 1 \
    $
    from which the result follows. (*NOTE*: We already the seen implication of the first part to the second part since $Delta gamma (u) + Delta zeta (u) <= 1$; otherwise the survival function given in @thm:ice would not be well-defined.)
]

= Efficient estimation

In this section, we derive the efficient influence function for $Psi_tau^g$.
The overall objective is to conduct inference for this parameter.
In particular, if $hat(Psi)_n$ is asymptotically linear at $P$ with influence function $phi_tau^* (P)$, i.e.,
$
    hat(Psi)_n - Psi_tau^g (P) = bb(P)_n phi_tau^* (dot; P) + o_P (n^(-1/2))
$
then $hat(Psi)_n$ is regular and (locally) nonparametically efficient (Chapter 25 of @vaart1998).
In this case, one can construct confidence intervals and hypothesis tests based on estimates of the influence function.
Therefore, our goal is to construct an asymptotically linear estimator
of $Psi_tau^g$ with influence function $phi_tau^* (P)$.

The efficient influence function in the nonparametric setting enables the use of machine learning methods to estimate the nuisance parameters
under certain regularity conditions to provide inference for the target parameter.
To achieve this, we need to debias our initial ICE-IPCW estimator either through double/debiased machine learning (@chernozhukovDoubleMachineLearning2018) or targeted minimum loss estimation (@laanTargetedMaximumLikelihood2006).
A method for constructing this estimator is presented in @section:onestep.

We derive the efficient influence function using the iterative representation given
in @eq:ipcw, working under the conclusions of @thm:ice, by finding the Gateaux derivative of the target parameter.
Note that this does not constitute a rigorous proof that @eq:eif
is the efficient influence function, but rather a heuristic argument.
To proceed, we introduce additional notation and define
$
    Qbar(k) (u  | history(k)) = p_(k a) (u | history(k-1)) + p_(k ell) (u | history(k-1)) + p_(k y) (u | history(k-1)), u < tau.
$ <eq:Qbaru>

A key feature of our approach is that the efficient influence function is expressed in terms of the martingale for the censoring process.
This representation is often computationally simpler, as it avoids the need to estimate multiple martingale terms, unlike the approach of @rytgaardContinuoustimeTargetedMinimum2022.
For a detailed comparison, we refer the reader to the appendix, where we show that our efficient influence function
is the same as the one derived by @rytgaardContinuoustimeTargetedMinimum2022 in the setting with no competing events (*NOTE:* The section in the appendix is incomplete).

#theorem("Efficient influence function")[
    Let for each $P in cal(M)$, $tilde(Lambda)^c_k (t | historycensored(k-1); P)$ be the corresponding
    cause-specific cumulative hazard function for the observed censoring
    for the $k$'th event. Suppose that there is a universal constant $C > 0$
    such that $tilde(Lambda)^c_k (tauend | historycensored(k-1); P) <= C$ for all $k = 1, dots, K$ and
    every $P in cal(M)$.
    The efficient influence function is then given by
    #text(size: 7.5pt)[$
        phi_tau^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrt(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1))) bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau}  \
            & times ((macron(Z)^a_(k,tau)- Qbar(k-1)) + integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (Qbar(k-1) (tau  | historycensored(k-1))-Qbar(k-1) (u  | historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u))\
                & +  Qbar(0) - Psi_tau^g (P),
    $<eq:eif>]
    where $tilde(M)^c (t) = tilde(N)^c (t) - tilde(Lambda)^c (t)$. Here $tilde(N)^c (t) = bb(1) {C <= t, T^e > t} = sum_(k=1)^K bb(1) {eventcensored(k) <= t, statuscensored(k) = c}$ is the censoring counting process,
    and $tilde(Lambda)^c (t) = sum_(k=1)^K bb(1) {eventcensored(k-1) < t <= eventcensored(k)} tilde(Lambda)_k^c (t | historycensored(k-1))$ is the cumulative censoring hazard process
    given in @section:censoring.
] <thm:eif>

#proof[
    Define
    $
        macron(Z)^a_(k,tau) (P | s, t_k, d_k, l_k, a_k, f_(k-1)) &= (bb(1) {t_k < s, d_k = ell})/(tilde(S)_P^c (t_k - | historycensored(k-1) = f_(k-1)))) Qbar(k)(P | a_(k-1), l_k, t_k, d_k, f_(k-1)) \
            &#h(1.5cm) + (bb(1) {t_k < s, d_k = a})/(tilde(S)_P^c (t_k - | historycensored(k-1) = f_(k-1)))  Qbar(k) (P | 1, l_(k-1), t_k, d_k, f_(k-1))\
            &#h(1.5cm) +  (bb(1) {t_k <= s, d_k = y})/(tilde(S)_P^c (t_k - | historycensored(k-1) = f_(k-1)))), s <= tau
    $ <eq:macronZ>
    and let 
    $
        Qbar(k-1) (P | s) = mean(P) [macron(Z)^a_(k,s) (P | s, eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k), historycensored(k-1)) | historycensored(k-1)], s <= tau
    $
    We compute the efficient influence function by calculating the derivative (Gateaux derivative) of $Psi_tau^g (P_epsilon)$
    with $P_epsilon = P + epsilon (delta_(O)-P)$ at $epsilon = 0$.
    //*NOTE:*
    //Formally, though, we have would have to do calculate the pathwise derivative for every parametric submodel $P_epsilon$ which goes through $P$ with every score function
    //in the tangent space. 
    //but the calculation would be nearly identical. 
    
    First note that:
    $
        &evaluated(partial / (partial epsilon))_(epsilon=0) Lambda_(k,epsilon)^c (dif t | historycensored(k-1) = f_(k-1)) \
            &=evaluated(partial / (partial epsilon))_(epsilon=0) (P_epsilon (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P_epsilon (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) \
            &=evaluated(partial / (partial epsilon))_(epsilon=0) (P_epsilon (eventcensored(k) in dif t, statuscensored(k) = c, historycensored(k-1) = f_(k-1))) / (P_epsilon (eventcensored(k) >= t, historycensored(k-1) = f_(k-1))) \
            &= (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) (bb(1) {eventcensored(k) in dif t, statuscensored(k) = c}-P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) \
            &- (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) (bb(1) {eventcensored(k) >= t} - P(eventcensored(k) >= t | historycensored(k-1) = f_(k-1)))(P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P (eventcensored(k) >= t| historycensored(k-1) = f_(k-1)))^2 \
            &= (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) (bb(1) {eventcensored(k) in dif t, statuscensored(k) = c}) / (P (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) - bb(1) {eventcensored(k) >= t} (P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P (eventcensored(k) >= t| historycensored(k-1) = f_(k-1)))^2 \
            &= (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) 1/(P (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) (bb(1) {eventcensored(k) in dif t, statuscensored(k) = c} - bb(1) {eventcensored(k) >= t} tilde(Lambda)^c_k (dif t | historycensored(k-1) = f_(k-1))) \
    $
    so that
    $
        &evaluated(partial / (partial epsilon))_(epsilon=0) product_(u in (s, t)) (1- tilde(Lambda)_(k,epsilon)^c (dif t | historycensored(k-1) = f_(k-1))) \
            &=evaluated(partial / (partial epsilon))_(epsilon=0) 1/(1-Delta cumhazardcensored(k, c, t))product_(u in (s, t]) (1- tilde(Lambda)_(k,epsilon)^c (dif t | historycensored(k-1) = f_(k-1))) \
            &=^((*))-1/(1-Delta tilde(Lambda)^c_(k,epsilon) (t | historycensored(k) = f_(k-1))) product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | historycensored(k-1) = f_(k-1))) integral_((s,t]) 1/(1 - Delta tilde(Lambda)_k^c (u | historycensored(k-1) = f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_k (dif u | historycensored(k-1) = f_(k-1)) \
            &quad +product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | historycensored(k-1) = f_(k-1))) 1/(1- Delta tilde(Lambda)_k^c (t | historycensored(k) = f_(k-1)))^2 evaluated(partial / (partial epsilon))_(epsilon=0) Delta tilde(Lambda)_(k,epsilon)^c (t | historycensored(k) = f_(k-1)) \
            &=-1/(1-Delta tilde(Lambda)^c_(k) (t | historycensored(k) = f_(k-1))) product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | historycensored(k-1) = f_(k-1))) integral_((s,t)) 1/(1 - Delta tilde(Lambda)_k^c (u | historycensored(k-1) = f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_k (dif u | historycensored(k-1) = f_(k-1)) \
            &quad -1/(1-Delta tilde(Lambda)^c_(k) (t | historycensored(k) = f_(k-1))) product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | historycensored(k-1) = f_(k-1))) integral_({t}) 1/(1 - Delta tilde(Lambda)_k^c (u | historycensored(k-1) = f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_k (dif u | historycensored(k-1) = f_(k-1)) \
            &quad +product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | historycensored(k-1) = f_(k-1))) 1/(1- Delta tilde(Lambda)_k^c (t | historycensored(k) = f_(k-1)))^2 evaluated(partial / (partial epsilon))_(epsilon=0) Delta tilde(Lambda)_(k,epsilon)^c (t | historycensored(k) = f_(k-1)) \
            &= -product_(u in (s, t)) (1- tilde(Lambda)_k^c (dif t | historycensored(k-1) = f_(k-1))) integral_((s,t)) 1/(1 - Delta tilde(Lambda)_k^c (u | historycensored(k-1) = f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_k (dif u | historycensored(k-1) = f_(k-1)).
    $
    In $(*)$, we use the product rule of differentiation and a well known result for product integration (Theorem 8 of @gill1990survey), which states that the (Hadamard) derivative of the product integral
    $mu mapsto product_(u in (s, t]) (1 + mu(u))$ in the direction $h$ is given by (for $mu$ is of uniformly bounded variation)// it's always finite because; but not necessarily uniformly bounded for all cumhazards; unless we assume that cumhazards themsleves are uniformly bounded.
    $
        &integral_((s,t]) product_(v in (s, u)) (1 + mu(dif v)) product_(v in (u, t]) (1 + mu(dif v)) h(dif u)
            &=product_(v in (s, t]) (1 + mu(dif v)) integral_((s,t]) 1/(1+Delta mu (u)) h(dif u)
    $
    Furthermore, for $P_epsilon = P + epsilon (delta_((X,Y)) - P)$, a simple calculation yields the well-known result
    $
        evaluated(partial / (partial epsilon))_(epsilon=0) mean(P_epsilon) [Y | X = x] = (delta_(X) (x)) / P(X = x) (Y - mean(P) [Y | X = x]).
    $
    Now, we are ready to recursively calculate the derivative
    $
        evaluated(partial / (partial epsilon))_(epsilon=0) macron(Q)^(a)_(k - 1, tau) (P_epsilon | a_(k-1), l_(k-1), t_(t-1), d_(k-1), f_(k-2))
    $
    which yields,
    $
        & evaluated(partial / (partial epsilon))_(epsilon=0) macron(Q)^(a)_(k - 1, tau) (P_epsilon | a_(k-1), l_(k-1), t_(t-1), d_(k-1), f_(k-2)) \
            &= delta_(historycensored(k-1) (f_(k-1)))/P(historycensored(k-1) = f_(k-1))  (macron(Z)^a_(k,tau) - Qbar(k-1) (tau, historycensored(k-1)) + \            
                &+ integral_(eventcensored(k-1))^(tau) macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) integral_((eventcensored(k-1), t_k)) 1/(1- Delta tilde(Lambda)_k^c (s | historycensored(k-1) = f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1))) (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
                &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | historycensored(k-1) = f_(k-1))) \
            &+ integral_(eventcensored(k-1))^(tau) (bb(1) {t_k < tau, d_(k) in {a, ell}})/(tilde(S)^c (t_k - | historycensored(k-1) = f_(k-1)))  ((bb(1) {a_k = 1}) / (densitytrt(t_(k), k)))^(bb(1) {d_(k) = a}) evaluated(partial / (partial epsilon))_(epsilon=0) lr(Qbar(k) (P_epsilon | a_(k), l_(k),t_(k), d_(k), f_(k-1))) \
            &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | historycensored(k-1) = f_(k-1)) 
    $
    Now note for the second term, we can write
    $
        &integral_(eventcensored(k-1))^(tau) macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) integral_((eventcensored(k-1),t_k)) 1/(1- Delta tilde(Lambda)_k^c (s | historycensored(k-1) = f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
            &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | historycensored(k-1) = f_(k-1))) \
            &= integral_(eventcensored(k-1))^(tau) integral_(s)^tau macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | historycensored(k-1) = f_(k-1)) \
            &#h(1.5cm) 1/(1- Delta tilde(Lambda)_k^c (s | historycensored(k-1) = f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
            &= integral_(eventcensored(k-1))^(tau) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
            &#h(1.5cm) 1/(1- Delta tilde(Lambda)_k^c (s | historycensored(k-1) = f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
                    &= integral_(eventcensored(k-1))^(tau) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
            &#h(1.5cm) 1/(tilde(S)^c (s | historycensored(k-1) = f_(k-1)) S (s - | historycensored(k-1) = f_(k-1))) (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s) \
    $
    by an exchange of integrals. Here, we apply the result of @thm:ice to get the last equation.
    Combining the results iteratively yields the result.
]

== One-step ICE-IPCW estimator <section:onestep>
// NOTE: A TMLE may be obtained similarly.
//For now, we recommend using the one step estimator and not the TMLE because the martingales are computationally intensive to estimate.
//This means that multiple TMLE updates may not be a good idea. 

In this section, we provide a one step estimator for the target parameter $Psi_tau^g$.
For a collection of estimators $eta = ({hat(Lambda)_k^x}, {hat(Lambda)_k^c}, {hat(pi)_k}, {nu_(k,tau)}, {tilde(nu)_(k,tau)}, hat(P)_(L(0)) )$,
we consider plug-in estimates of the efficient influence function
$
    phi_tau^* (O; eta) &= (bb(1) {treat(0) = 1})/ (hat(pi)_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (pi_j (eventcensored(j), historycensored(j-1))))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) hat(S)^(c) (eventcensored(j)- | historycensored(j-1))) bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} \
        & times ((macron(Z)^a_(k,tau) (hat(S)_(k-1)^(c), nu_(k,tau)) - nu_(k-1,tau)) \
            &qquad+ integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1)(tau | historycensored(k-1))-mu_(k-1)(u | historycensored(k-1))) 1/(hat(S)^(c) (u | historycensored(k-1)) hat(S) (u- | historycensored(k-1))) (tilde(N)^c (dif u) - tilde(Lambda)^c (dif u | historycensored(k-1)))) \
        & + nu_(0,tau) (1, L(0)) - hat(P)_(L(0)) [ nu_(0,tau) (1, dot)]
$ <eq:onestep-eif>
where
$
    mu_k (u | historycensored(k)) &= integral_(eventcensored(k))^(u) prodint2(s, eventcensored(k), u) (1-sum_(x=a,l,d,y) hat(Lambda)_(k)^x (dif s | historycensored(k))) \
        &times [hat(Lambda)^y_(k+1) (dif s | historycensored(k)) + bb(1) {s < u} tilde(nu)_(k+1,tau)(1, s, a, history(k)) hat(Lambda)^a_(k+1) (dif s | historycensored(k)) + bb(1) {s < u} tilde(nu)_(k+1, tau)(treat(k-1), s, ell, history(k)) hat(Lambda)^ell_(k+1) (dif s | historycensored(k))].
$ <eq:mu>

Here, we let $tilde(nu)_(k, tau) (u | f_k)$ be an estimate of $QbarL(k) (u |f_k) := mean(P) [Qbar(k) (u | historycensored(k)) | treatcensored(k) = a_k, statuscensored(k) = d_k, historycensored(k-1) = f_(k-1)]$,
let $nu_(k,tau) (f_k)$ be an estimate of $Qbar(k) (tau | f_k)$, and let $hat(P)_(L(0))$ be an estimate of $P_(L(0))$, the distribution of the covariates at time 0.
We use the notation $macron(Z)^a_(k,tau) (tilde(S)_(k-1)^(c), nu_(k,tau))$ to explicitly denote the dependency on $tilde(S)_(k-1)^(c)$ and $nu_(k,tau)$.

We will now describe how to estimate the efficient influence function in practice.
Overall, we consider the same procedure as in @alg:ipcwice with additional steps:
1. For ${nu_(k,tau) (f_k)}$, use the procedure described in @alg:ipcwice.
2. For ${tilde(nu)_(k,tau) (f_k)}$ use a completely similar procedure to the one given in @alg:ipcwice
   using the estimator $nu_(k+1,tau)$ to obtain $tilde(nu)_(k,tau)$.
   Now we do not include the latest time varying covariate $covariatecensored(k)$
   in the regression, so that
   $tilde(nu)_(k-1,tau) = bb(E)_(hat(P)) [macron(Z)^a_(k,tau) (hat(S)_(k-1)^(c), nu_(k,tau)) | treatcensored(k) = a_k, statuscensored(k) = d_k, historycensored(k-1) = f_(k-1)]$.
3. Find ${hat(Lambda)_k^x}$ for $x=a,ell,d,y$ and ${hat(Lambda)^c_k}$ using step 1 in @alg:ipcwice.
4. Obtain an estimator of the propensity score ${pi_k (t, f_(k-1))}$ by regressing
   $treatcensored(k)$ on $(eventcensored(k), historycensored(k-1))$ among
   subjects with $statuscensored(k) = a$ and $statuscensored(k-1) in {a, ell}$ for each $k$
   and for $k=0$ estimate $pi_0 (L(0))$ by regressing $treat(0)$ on $L(0)$.
5. Use the estimates $tilde(nu)_(k,tau) (f_k)$ and the estimates of $hat(Lambda)_(k)^x, x=a,ell,d,y$ to numerically compute $mu_(k-1)$
   via @eq:mu.
6. Use the estimated survival functions from the cumulative hazards in step 3 to compute the martingale term in @eq:onestep-eif.
   See also @section:censmg for details on how to approximately compute the censoring martingale term.
7. Substitute the rest of the estimates into @eq:onestep-eif and obtain the estimate of the efficient influence function.

There are multiple computational aspects of the stated procedure
that should be addressed. 
First note that $Qbar(k) (tau)$ is estimated twice.
This redundancy is intentional: it ensures both the computability of the terms involved in the censoring martingale and that we can use $nu_(k,tau)$
required for subsequent iterations of the algorithm (avoiding the high dimensionality of the integrals as discussed in @section:estimand).
//and the non-martingale terms in @eq:onestep-eif in the following iterations.

Our decision to use $nu_(k,tau)$ rather than $mu_(k,tau)$ as an estimator for the regression terms ($macron(Z)^a_(k,tau) - Qbar(k-1)$) in @eq:onestep-eif is motivated by practical considerations.
In particular, numerical integration may yield less accurate results due to the need to compute $Lambda_k^x$ for $x=a,ell,d,y$.
In practice, the contribution of the censoring martingale to the efficient influence function is typically small.
As such, a simplified procedure that excludes the censoring martingale term or one that computes the censoring martingale term only at a sparse grid of time points may offer substantial computational efficacy
with minimal bias.

It is also more efficient computationally to use $nu_(k,tau)$ rather than $mu_(k,tau)$. To see this for $k=1$, note that we would not only need to compute $mu_(0, tau) (1, L_i (0))$ for $i in {1, dots, n}$ with $A_i (0) = 1$,
but for all $i = 1, dots, n$ to estimate the term in the efficient influence function given by $mu_(0, tau) (1, L_i (0))$.
//This simplification leads to slightly conservative standard error estimates.

We have also elected not to estimate @eq:Qbaru using the procedure described in the algorithm in @alg:ipcwice (ICE-IPCW), as it
may be prohibitively expensive to do so even along a sparse grid of time points.
Moreover, the resulting estimators are not guaranteed to be monotone in $u$
which $Qbar(k) (u | historycensored(k))$ is.

Another alternative is to use parametric/semi-parametric models
for the estimation of the cumulative cause-specific hazard functions
for the censoring. In that case, we may not actually need to debias
the censoring martingale, but can still apply machine learning methods
to iterated regressions.

//For instance, the ICE-IPCW approach would be computationally infeasible along a dense grid of time points.
Now, we turn to the resulting one-step procedure. 
For the ICE-IPCW estimator $hat(Psi)^0_n$, we let $hat(eta) = ({hat(Lambda)^x_k}_(k,x), {hat(Lambda)_k^c}, {hat(pi)_k}_(k), {hat(nu)_(k,tau)}_(k), {tilde(nu)_(k,tau)}_k, bb(P)_n)$
be a given estimator of the nuisance parameters occuring in $phi_tau^* (O; eta)$,
where $bb(P)_n$ denotes the empirical distribution,
and consider the decomposition
$
    hat(Psi)^0_n - Psi_tau^g (P) &= bb(P)_n phi_tau^* (dot; eta) \
        &-bb(P)_n phi_tau^* (dot; hat(eta)) \
        &+ (bb(P)_n - P) (phi_tau^* (dot; hat(eta)) - phi_tau^* (dot; eta)) \
        &+ R_2 (eta, hat(eta)),
$
where
$
    R_2 (eta, eta') &= P_eta [phi_tau^* (dot; eta')] + Psi^"obs"_tau (eta') - Psi_tau^g (eta)
$
and $Psi_tau^g (hat(eta))  = bb(P)_n [nu_(0, tau) (1, dot)]$.
We consider one-step estimation, that is
$
    hat(Psi)_n &= hat(Psi)^0_n + bb(P)_n phi_tau^* (dot; hat(eta)).
$
This means that to show that
$hat(Psi)_n - Psi_tau^g (P) &= bb(P)_n phi_tau^* (dot; eta) + o_P (n^(-1/2))$,
we must show that
$
    R_2 (eta, hat(eta)) = o_P (n^(-1/2)), 
$ <eq:remainder>
and that the empirical process term fulfills
$
    (bb(P)_n - P) (phi_tau^* (dot; hat(eta)) - phi_tau^* (dot; eta)) = o_P (n^(-1/2)).
$ <eq:empirical>

We first discuss how to show @eq:empirical.
This can be shown (Lemma 19.24 of @vaart1998) if
1. $phi_tau^* (dot; hat(eta)) in cal(Z)$ for some $P$-Donsker class $cal(Z)$ of functions with probability tending to 1, and
2. $||phi_tau^* (dot; hat(eta)) - phi_tau^* (dot; eta)||_(L^2_P (O)) = o_P (1)$,
   with $||f||_(L^2_P (O)) = (mean(P) [f (O)^2])^(1/2)$.

Simple sufficient conditions for this to happen are provided in Lemma *NOT DONE YET*.
Alternatively, one may use cross-fitting/sample splitting (@chernozhukovDoubleMachineLearning2018) to ensure that the empirical process term is negligible.

To obtain the rates in @eq:remainder, we find the second order remainder term $R_2 (eta_0, eta)$
and show that it has a product structure (@thm:remainder). This allows us to use estimators
which need only convert at $L_2 (P)$-rates of at least $o_P (n^(-1/4))$ under regularity conditions.
//For instance, the term involving $V_k$ can be bounded by
//$
//    &lr(|integral_(eventcensored(k - 1))^(tau) integral_((eventcensored(k-1),u)) ((S_0 (s- | historycensored(k-1))) / (S (s- | historycensored(k-1))) - 1)  (tilde(S)^c_0 (s- | historycensored(k-1)))/(tilde(S)^c (s | historycensored(k-1))) (tilde(Lambda)^c_(k,0) (d s | historycensored(k-1)) - tilde(Lambda)_k^c (d s | historycensored(k-1))) (mu_(k-1, tau) (d u |historycensored(k-1)))|) \
//        &<= mu_(k-1, tau) (tau) sup_(u in (eventcensored(k-1), tau]) lr(| integral_((eventcensored(k-1),u)) ((S_0 (s- | history(k-1))) / (S (s- | history(k-1))) - 1)  (tilde(S)^c_0 (s- | history(k-1)))/(tilde(S)^c (s | history(k-1))) (tilde(Lambda)^c_(k,0) (d s | history(k-1)) - tilde(Lambda)_k^c (d s | history(k-1))) |)  \
//$
//The desired rate conditions may then be easier.
// Write more explicitly for mu, where a = tilde(nu) and b = S (s) Lambda 
// Because: int a d b - int hat a hat d b = - int hat a (hat d b - d b) + int a d b - int hat a d b
#theorem("Second order remainder")[
    Let $eta_0 = ({Lambda_(k,0)^x}_(k,x), {tilde(Lambda)_(k,0)^c}_(k), {pi_(0,k)}_(k), {Qbar(k)}_(k), {QbarL(k)}_k, P_(0,L(0)) )$ be the true parameter values
    and let $eta = ({Lambda_(k)^x}_(k,x), {tilde(Lambda)_(k)^c}_(k), {pi_k}_(k), {nu_(k,tau)}_(k), {tilde(nu)_(k,tau)}_k, P'_(L(0)) )$.
    The remainder term $R_2 (eta_0, eta)$ is given by
    $
        R_2 (eta_0, eta)&= sum_(k=1)^(K-1) integral bb(1) {t_1 < dots < t_(k) < tau} bb(1) {a_0 = dots = a_(k) = 1} \
            &(pi_(0,0) (l_0))/ (pi_(0) (l_0)) product_(j = 1)^(k) ((pi_(0,j) (t_j, f_(j-1))) / (pi_(j) (t_j, f_(j-1))))^(bb(1) {d_j = a}) (1)/(tilde(S)^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} z_k (f_(k)) P_(0,historycensored(k)) (dif f_(k)) \
            &quad + integral bb(1) {a_0 = 1} z_0 (a_0, l_(0)) P_(0, L(0)) (dif l_0) \
    $
    where
    $
        z_k (f_k) &= (((pi_(k,0) (t_(k), f_(k-1)))/ (pi_(k) (t_k, f_(k-1))))^(bb(1) {d_k = a})-1) (Qbar(k) (f_(k))- nu_(k, tau) (f_(k))) \
            &+((pi_(k,0) (t_k, f_(k-1)))/ (pi_(k) (t_k, f_(k-1))))^(bb(1) {d_(k) = a})integral_(t_(k ))^(tau) ((tilde(S)^c_0 (u- | f_(k))) / (tilde(S)^c (u- | f_(k)))-1) (Qbar(k) (d u | f_(k)) - nu^*_(k, tau) (d u |f_(k))) \
            &+((pi_(k,0) (t_k, f_(k-1)))/ (pi_(k) (t_k, f_(k-1))))^(bb(1) {d_(k) = a}) integral_(t_(k ))^(tau) V_(k+1) (u, f_(k)) nu^*_(k, tau) (d u |f_(k)),
    $
    for $k >= 1$ and for $k=0$
    $
        z_0 (1, l_0) &= ((pi_(0,0) (l_(0)))/ (pi_(0) (l_0))-1) (Qbar(0) (1, l_0)- nu_(0, tau) (1, l_0)) \
            &+ (pi_(0,0) (l_0))/ (pi_(0) (l_0)) integral_(0)^(tau) ((tilde(S)^c_0 (s- | 1,l_0)) / (tilde(S)^c (s- | 1,l_0))-1) (Qbar(0) (d s | 1,l_0) - nu^*_(0, tau) (d s | 1,l_0)) \
            &+ (pi_(0,0) (l_0))/ (pi_(0) (l_0)) integral_(0)^(tau) V_1 (u, 1, l_0) nu^*_(0, tau) (d u | 1,l_0),
    $
    and $V_k (u, f_(k-1)) = integral_((t_(k-1),u)) ((S_0 (s- | f_(k-1))) / (S (s- | f_(k-1))) - 1)  (tilde(S)^c_0 (s- | f_(k-1)))/(tilde(S)^c (s | f_(k-1))) (tilde(Lambda)^c_(k,0) (d s | f_(k-1)) - tilde(Lambda)_k^c (d s | f_(k-1)))$.
] <thm:remainder>
#proof[
    First define $phi_(k,tau)^* (O;eta)$ for $k > 0$ to be
    the $k$'th term in the efficient influence function given in @eq:eif,
    and let $phi_(0,tau)^* (O; eta) = nu_(0) (1, covariate(0)) - Psi^"obs"_tau (eta)$, so that
    $phi_tau^* (O; P) = sum_(k=0)^(K) phi_k^* (O; P)$.
    
    Then, we first note that 
    $
        mean(P_0) [phi_(0,tau)^* (O; eta)] + Psi_tau^g (eta) - Psi_tau^g (eta_0) =  mean(P_0)[nu_(0) (1,covariate(0)) - Qbar(0) (1,covariate(0))].
    $ <eq:cancelterm0>
Apply the law of iterated expectation to the efficient influence function in @eq:eif to get
$
    mean(P_0) [phi_(k,tau)^* (O;P)] &= integral bb(1) {t_1 < dots < t_(k-1) < tau} bb(1) {a_0 = dots = a_(k-1) = 1} (pi_(0,0) (l_0))/ (pi_0 (l_0)) \
        &qquad times product_(j = 1)^(k-1) ((pi_(0,j) (t_k, f_(j-1))) / (pi_(j) (t_k, f_(j-1))))^(bb(1) {d_j = a}) (1)/(  tilde(S)^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} \
    & qquad times mean(P) [h_k (historycensored(k)) | historycensored(k-1) = f_(k-1)] P_(0, historycensored(k-1)) (dif f_(k-1))
$          
where
$
    h_k (historycensored(k)) = macron(Z)^a_(k,tau) (tilde(S), nu_k)- nu_(k-1) + integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau  | historycensored(k-1))-mu_(k-1) (u  | historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u).
$
Now note that
$
    & mean(P_0) [h_k (historycensored(k)) | historycensored(k-1)] \
            &= mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c_0,  Qbar(k))) | historycensored(k-1)] - nu_(k-1, tau) (historycensored(k-1)) \
            &+ mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, nu_(k)) | historycensored(k-1)]- mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, Qbar(k)) | historycensored(k-1)] \
            &+mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, Qbar(k)) | historycensored(k-1)] - mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c_0,  Qbar(k)) | historycensored(k-1)] \
        &+ mean(P_0) [ integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u) | historycensored(k-1)] \
$ <eq:hk>

    We shall need the following auxilliary result.
#lemma[
    $
        &mean(P_0) [ integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u) | historycensored(k-1)] \
            &=integral_(eventcensored(k - 1))^(tau) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) (tilde(S)^c_0 (u- | historycensored(k-1)) S_0 (u- | historycensored(k-1)))/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) (tilde(Lambda)^c_(k,0) (d u | historycensored(k-1)) - tilde(Lambda)_k^c (d u | historycensored(k-1)))
    $
] <lemma:mgterm>
    #proof[
We first note that
        $
        &mean(P_0) [ integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)^c (dif u) | historycensored(k-1)] \
        &=mean(P_0) [ integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)^c_(k) (dif u | historycensored(k-1)) | historycensored(k-1)] \
            &= mean(P_0) [integral_(eventcensored(k - 1))^(tau) bb(1) {eventcensored(k) <= t} \
                &qquad times (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1)) ) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)^c_(k) (dif u | historycensored(k-1)) | historycensored(k-1)] \
            &= integral_(eventcensored(k - 1))^(tau) mean(P_0) [bb(1) {eventcensored(k) <= t} | historycensored(k-1)] (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)^c_(k) (dif u | historycensored(k-1))  \
            &=integral_(eventcensored(k - 1))^(tau) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) (tilde(S)^c_0 (u- | historycensored(k-1)) S_0 (u- | historycensored(k-1)))/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)_k^c (d u | historycensored(k-1))
        $ <eq:test>
        by simply interchanging the integral and the expectation (see for instance Lemma 3.1.4 of @last1995marked).
Finally, let $A in historycensored(k-1)$.
        Then, using the compensator of $tilde(N)^c (t)$ under $P_0$ is $tilde(Lambda)^c_0 = sum_(k=1)^K bb(1) {eventcensored(k-1) < t <= eventcensored(k)} tilde(Lambda)_(k,0)^c (dif t | historycensored(k-1))$
         and that $bb(1) {A} bb(1) {eventcensored(k-1) < s <= eventcensored(k)}$ is predictable, we have
    $
        &mean(P_0) [bb(1) {A} bb(1) {eventcensored(k-1) < tau} integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(N)^c (dif t)] \
            &=mean(P_0) [bb(1) {A} bb(1) {eventcensored(k-1) < tau} integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)_0^c (dif t)] \
            &=mean(P_0) [bb(1) {A} bb(1) {eventcensored(k-1) < tau} integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)_(k,0)^c (dif t | historycensored(k-1))] \
    $
    from which we conclude that
    $
        &mean(P_0) [bb(1) {eventcensored(k-1) < tau} integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(N)^c (dif t) | historycensored(k-1)] \
            &= mean(P_0) [bb(1) {eventcensored(k-1) < tau} integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)^c_(0,k) (dif t | historycensored(k-1)) | historycensored(k-1)] \
            &= integral_(eventcensored(k - 1))^(tau) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) (tilde(S)^c_0 (u- | historycensored(k-1)) S_0 (u- | historycensored(k-1)))/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)_(k,0)^c (d u | historycensored(k-1)) \
    $
        where the last equality follows from the same argument as in @eq:test.
    ]
    By an exchange of integrals, it follows that 
$
    &integral_(eventcensored(k - 1))^(tau) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) (tilde(S)^c_0 (u- | historycensored(k-1)) S_0 (u- | historycensored(k-1)))/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) (tilde(Lambda)^c_(k,0) (d u | historycensored(k-1)) - tilde(Lambda)_k^c (d u | historycensored(k-1))) \
        &=integral_(eventcensored(k - 1))^(tau) integral_u^tau mu_(k-1) (dif s | historycensored(k-1)) (tilde(S)^c_0 (u- | historycensored(k-1)) S_0 (u- | historycensored(k-1)))/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) (tilde(Lambda)^c_(k,0) (d u | historycensored(k-1)) - tilde(Lambda)_k^c (d u | historycensored(k-1))) \
        &=integral_(eventcensored(k - 1))^(tau) integral_((eventcensored(k-1),s)) (tilde(S)^c_0 (u- | historycensored(k-1)) S_0 (u- | historycensored(k-1)))/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) (tilde(Lambda)^c_(k,0) (dif u | historycensored(k-1)) - tilde(Lambda)_k^c (dif u | historycensored(k-1))) mu_(k-1, tau) (dif s |historycensored(k-1)) \
        &=integral_(eventcensored(k - 1))^(tau) integral_((eventcensored(k-1),s)) ((S_0 (u- | historycensored(k-1))) / (S (u- | historycensored(k-1))) - 1)  (tilde(S)^c_0 (u- | historycensored(k-1)))/(tilde(S)^c (u | historycensored(k-1))) (tilde(Lambda)^c_(k,0) (dif u | historycensored(k-1)) - tilde(Lambda)_k^c (dif u | historycensored(k-1))) mu_(k-1, tau) (dif s |historycensored(k-1)) \
        &quad +integral_(eventcensored(k - 1))^(tau) integral_((eventcensored(k-1),s)) (tilde(S)^c_0 (u- | historycensored(k-1))) / (tilde(S)^c (u | historycensored(k-1))) (tilde(Lambda)^c_(k,0) (dif u | historycensored(k-1)) - tilde(Lambda)_k^c (dif u | historycensored(k-1))) mu_(k-1, tau) (dif s |historycensored(k-1)) \
        &=integral_(eventcensored(k - 1))^(tau) integral_((eventcensored(k-1),s)) ((S_0 (u- | historycensored(k-1))) / (S (u- | historycensored(k-1))) - 1)  (tilde(S)^c_0 (u- | historycensored(k-1)))/(tilde(S)^c (u | historycensored(k-1))) (tilde(Lambda)^c_(k,0) (dif u | historycensored(k-1)) - tilde(Lambda)_k^c (dif u | historycensored(k-1))) mu_(k-1, tau) (dif s |historycensored(k-1)) \
        &quad -integral_(eventcensored(k - 1))^(tau) ((tilde(S)^c_0 (s- | historycensored(k-1))) / (tilde(S)^c (s- | historycensored(k-1)))-1) mu_(k-1, tau) (dif s |historycensored(k-1))
$
    where we apply the Duhamel equation (taking the left limits of Equation (2.6.5) of @andersenStatisticalModelsBased1993) in the last equality.
    //Since
    //$
    //    &mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, QbarL(k)) | historycensored(k-1)] - mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c_0,  QbarL(k)) | historycensored(k-1)] \
    //        &=mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, Qbar(k)) | historycensored(k-1)] - mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c_0,  Qbar(k)) | historycensored(k-1)],
    //$
    Since 
    $
        &mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, Qbar(k)) | historycensored(k-1)] - mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c_0,  Qbar(k)) | historycensored(k-1)] \
            &=integral_(eventcensored(k-1))^tau ((tilde(S)_0^c (u - |historycensored(k-1)))/(tilde(S)^c (u - | historycensored(k-1))) - 1) Qbar(k-1) (dif u | historycensored(k-1)),
    $
it follows from @eq:hk and @lemma:mgterm that
$
    & mean(P_0) [h_k (historycensored(k)) | historycensored(k-1)] \
        &=mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c_0,  Qbar(k))) | historycensored(k-1)] - nu_(k-1, tau) (historycensored(k-1)) \
        &quad + mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, nu_(k)) | historycensored(k-1)]- mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, Qbar(k)) | historycensored(k-1)] \
        &quad+integral_(eventcensored(k - 1))^(tau) ((tilde(S)^c_0 (u- | historycensored(k-1))) / (tilde(S)^c (u- | historycensored(k-1)))-1) (Qbar(k-1) (d u | historycensored(k-1)) - mu_(k-1, tau) (d u |historycensored(k-1))) \
        &quad+integral_(eventcensored(k - 1))^(tau) integral_((eventcensored(k-1), u)) ((S_0 (s- | historycensored(k-1))) / (S (s- | historycensored(k-1))) - 1)  (tilde(S)^c_0 (s- | historycensored(k-1)))/(tilde(S)^c (s | historycensored(k-1))) (tilde(Lambda)^c_(k,0) (d s | historycensored(k-1)) - tilde(Lambda)_k^c (d s | historycensored(k-1))) mu_(k-1, tau) (d u |historycensored(k-1)) \
$ <eq:decomposeProofRemainder>

    Since it also holds for $k >= 1$ that,
    $
        &integral bb(1) {t_1 < dots < t_(k-1) < tau} bb(1) {a_0 = dots= a_(k-1) = 1}  (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k-1) ((pi_(0,j) (t_k, f_(j-1))) / (pi_(j) (t_k, f_(j-1))))^(bb(1) {d_j = a}) (1)/( product_(j=1)^(k-1) tilde(S)^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} \
            &qquad times mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, nu_(k)) | historycensored(k-1) = f_(k-1)]- mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, Qbar(k)) | historycensored(k-1) = f_(k-1)] P_(0,historycensored(k-1)) (d f_(k-1)) \
            &= integral bb(1) {t_1 < dots < t_(k-1) < tau} bb(1) {a_0 = dots= a_(k-1) = 1}  (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k-1) ((pi_(0,j) (t_k, f_(j-1))) / (pi_(j) (t_k, f_(j-1))))^(bb(1) {d_j = a}) (1)/( product_(j=1)^(k-1) tilde(S)^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} \
            &quad integral bb(1) {t_k < tau} bb(1) {a_k = 1} (1)/( tilde(S)^c (t_k- | f_(k-1))) \
        &qquad times sum_(d_k=a, ell) (nu_(k) (a_k, l_k, t_k, d_k, f_(k-1)) - Qbar(k) (a_k, l_k, t_k, d_k, f_(k-1)))
        P_(0,(treatcensored(k), covariatecensored(k), eventcensored(k), statuscensored(k)) | historycensored(k-1)) (dif f_k | f_(k-1)) P_(0,historycensored(k-1)) (d f_(k-1)) \
                        &= integral bb(1) {t_1 < dots < t_k < tau} bb(1) {a_0 = dots= a_(k) = 1}  (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k-1) ((pi_(0,j) (t_k, f_(j-1))) / (pi_(j) (t_k, f_(j-1))))^(bb(1) {d_j = a}) (1)/( product_(j=1)^(k) tilde(S)^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k) in {ell, a}} \
            &qquad times (nu_k (f_k) - Qbar(k) (f_k)) P_(0,historycensored(k)) (d f_(k))

    $
we have that  
$
    &integral bb(1) {t_1 < dots < t_(k) < tau} bb(1) {a_0 = dots= a_k = 1} (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k) ((pi_(0,j) (t_j, f_(j-1))) / (pi_(j) (t_j, f_(j-1))))^(bb(1) {d_j = a}) (1)/( product_(j=1)^(k) tilde(S)^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k) in {ell, a}} \
        & qquad times (mean(P_0) [macron(Z)^a_(k+1,tau) (tilde(S)^c_0,  Qbar(k+1)) | historycensored(k) = f_k] - nu_(k, tau) (f_k)) P_(0,historycensored(k)) (d f_(k)) \
        &+integral bb(1) {t_1 < dots < t_(k-1) < tau} bb(1) {a_0 = dots= a_(k-1) = 1}  (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k-1) ((pi_(0,j) (t_k, f_(j-1))) / (pi_(j) (t_k, f_(j-1))))^(bb(1) {d_j = a}) (1)/( product_(j=1)^(k-1) tilde(S)^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} \
        &qquad times mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, nu_(k)) | historycensored(k-1) = f_(k-1)]- mean(P_0) [macron(Z)^a_(k,tau) (tilde(S)^c, Qbar(k)) | historycensored(k-1) = f_(k-1)] P_(0,historycensored(k-1)) (d f_(k-1)) \
        &=integral bb(1) {t_1 < dots < t_(k) < tau} bb(1) {a_0 = dots= a_k = 1}  (pi_(0,0) (l_0))/ (pi_0 (l_0)) \
        &qquad product_(j = 1)^(k-1) ((pi_(0,j) (t_j, f_(k-1))) / (pi_(j) (t_j, f_(j-1))))^(bb(1) {d_k = a}) (((pi_(0,k) (k_j, f_(k-1))) / (pi_(k) (t_k, f_(k-1))))^(bb(1) {d_k = a})-1) (1)/( product_(j=1)^(k) tilde(S)^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k) in {ell, a}} \
        & qquad times (Qbar(k) (f_k) - nu_(k, tau) (f_k)) P_(0,historycensored(k)) (d f_(k)).
$ <eq:canceltermk>
    By combining @eq:cancelterm0, @eq:decomposeProofRemainder and @eq:canceltermk, we are done.  
]

== Algorithm for the calculation of censoring martingale <section:censmg>

//Overall, the described procedure in pseudo-code is given in #smallcaps("debiasIceIpcw") and
//we the algorithm #smallcaps("getCensoringMartingale") describes how to compute the outer integral
//for the martingale term on a fine grid of time points.

// #algo(
//   title: "debiasIceIpcw",
//     parameters: ($cal(D)_n$, $tau$, $cal(L)_o$, $cal(L)_h$, $cal(L)_pi$ )
// )[
//     $K_tau <- $#smallcaps("getLastEvent")$ (cal(D)_n, tau)$ #comment[get the last non-terminal event number before time $tau$]\
//     $hat("IF") <- 0$ \
//     ${hat(pi)_(k), hat(Lambda)_(k)^c, hat(Lambda)_(k)^y, hat(Lambda)_(k)^a,  hat(Lambda)_(k)^d,  hat(Lambda)^ell_(k)}_k <- $#smallcaps("fitPropensityScores")$ (cal(D)_n, cal(L)_h, cal(L)_pi)$ \
//     for $k <- K_tau$ to $0$: #i\
//     $R_(k) <- {i in {1, dots, n} | macron(Delta)_(k,i) != {y, d, c},  macron(T)_(k,i) < tau}$ \
//     $(macron(T)_(k+1), macron(Delta)_(k+1), historycensored(k), historycensored(k+1)) <- cal(D)_(n)[R_(k), (macron(T)_(k+1), macron(Delta)_(k+1), historycensored(k), historycensored(k+1))]$ \
//     \
//     $I_(k+1) <- eventcensored(k+1) - eventcensored(k)$ \
//     #comment[calculate survival function for the censoring process for subjects] \
//     $hat(S)^(c-)_(k+1) <- product_(s in (0, I_(k+1)[R_k,])) (1 - hat(Lambda)_(k+1)^c (s | historycensored(k)))$ \
//     \
//     $hat(S)^(c)_(k+1) <- hat(S)^(c-)_(k+1) (1- Delta hat(Lambda)_(k+1)^c (I_(k+1)[R_k,] | historycensored(k)))$ \

//     #comment[calculate survival function for uncensored event] \
//     $hat(S)^(-)_(k+1) <- product_(s in (0, I_(k+1)[R_k,])) (1 - sum_(x=a,ell,d,y) hat(Lambda)_(k+1)^x (s | historycensored(k)))$ \
//     $historycensored(k+1)[, (A(0), dots, A(eventcensored(k+1)))] <- 1$ \
//     $hat(Z)^a_(k+1) <- (bb(1) {macron(T)_(k+1) <= tau, macron(Delta)_(k+1) = y}) / (hat(S)^(c-)_(k+1))$ \
//     if $k < K_tau$: #i\
//     $hat(Z)^a_(k+1) <- hat(Z)^a_(k+1) + (bb(1) {macron(T)_(k+1) < tau, macron(Delta)_(k+1) in {a, ell}} hat(nu)_(k+1) (historycensored(k+1))) / (hat(S)^(c-)_(k+1))$ #comment[calculate the subject-specific pseudo-outcome using $hat(nu)_(k+1)$ to predict] #d\
//     $hat(nu)_(k) <- cal(L)_o (hat(Z)^a_(k+1),  historycensored(k))$ #comment[regress the pseudo-outcome on the history to obtain a prediction function]\
//     $cal(F)^((tilde(beta), -L))_(eventcensored(k)) <- historycensored(k)[, -covariatecensored(k)]$ \
//     $tilde(nu)_(k,tau) <- cal(L)_o (hat(Z)^a_(k+1),  cal(F)^((tilde(beta), -L))_(eventcensored(k)))$\

//     $hat("IPW")_(k+1) <- (bb(1) {treat(0) = 1})/ (hat(pi)_0 (L(0))) product_(j = 1)^(k-1) ((bb(1) {treat(j) = 1}) / (hat(pi)_j (eventcensored(j),  historycensored(j-1))))^(bb(1) {status(j) = a}) 1/( product_(j=1)^(k-1) hat(S)^c (eventcensored(j)- | historycensored(j-1))) bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau}$ \
//     $"MG"_(k+1) <- $#smallcaps("getCensoringMartingale")$ ({t_1, dots, t_k}, {macron(T)_(k+1, i)}_i, {macron(T)_(k, i)}_i, historycensored(k), tilde(nu)_(k+1, tau), {A(macron(T)_(k, i))}_i, {Delta_(k+1,i)}_i)$ \
//     $hat("IF")_(k+1) <- hat("IPW")_(k+1)(hat(Z)^a_(k+1) - hat(nu)_(k) + "MG"_(k+1))$ #d \
//     $hat(Psi)^0_n <- 1/n sum_(i=1)^n hat(nu)_(0) (L_i (0), 1)$ \
//     $hat("IF") <- sum_(j=0)^(K) hat("IF")_(j+1) +  hat(nu)_(0) (L (0), 1) - hat(Psi)^0_n$ \
//     $hat(Psi)_n <- hat(Psi)^0_n + 1/n sum_(i=1)^n hat("IF") [i] $\
//     return #$(hat(Psi)_n, hat("IF"))$ 
// ]

In this subsection, we present an algorithm for computing the martingale term in @eq:onestep-eif along a specified time grid ${t_1, dots, t_m}$ at iteration $k$ of the influence function estimation procedure.
In Steps 6, 8, 10, and 11 of the algorithm, we may use coarse approximations for the survival function and the associated integrals.
For example, one may approximate the survival function using the exponential function or apply numerical integration techniques such as Simpson’s rule to simplify computation.
Note that we integrate over time on the interarrival scale.
This means that we usually select $t_1=0$ and $t_m <= tau - min_i macron(T)_(k+1,i)$.

#algo(
    title: "censoringMartingale",
    indent-size: 7pt,
      column-gutter: 2pt,
    parameters: ($k$, ${t_1, dots, t_m}$, ${macron(T)_(k,i), macron(T)_(k+1,i)}$, ${cal(F)_(macron(T)_(k,i))}$, ${hat(Lambda)_(k+1)^x}_x$, $tilde(nu)_(k+1)$, ${A(macron(T)_(k,i))}$, ${macron(Delta)_(k+1,i)}$)
)[
    for $i = 1, dots, n$: #i\
    $j_"max" <- max {v | t_v <= tau - macron(T)_(k,i)}$ \
    $hat(nu)_( tau)^y (0) <- hat(nu)_(tau)^a (0) <- hat(nu)_(tau)^ell (0) <- t_0 <- hat(M)^c (0) <- 0$ \
    $hat(S)_0 <- 1$ \
    for $j = 1, dots, j_"max"$ #i \
    $hat(S) (s-) <- product_(v in [t_(j-1), s)) (1-sum_(x=a,l,d,y) hat(Lambda)_(k+1)^x (dif v | cal(F)_(macron(T)_(k,i))))$ \
    $hat(S)_j <- hat(S)_(j-1) dot S(t_j)$\
    $hat(nu)_(tau)^y (t_j) <- hat(nu)_(tau)^y (t_(j-1)) + hat(S)_(j-1) integral_((t_(j-1), t_j]) hat(S)(s-) hat(Lambda)_(k+1)^y (dif s | cal(F)_(macron(T)_(k,i))) $ \
    if $k < K_tau$: #i\
    $hat(nu)_(tau)^a (t_j) <- hat(nu)_(tau)^a (t_(j-1)) + hat(S)_(j-1) integral_((t_(j-1), t_j)) hat(S)(s-) tilde(nu)_(k+1) (1, s + macron(T)_(k+1,i), a, cal(F)_(macron(T)_(k,i))) hat(Lambda)_(k+1)^a (dif s | cal(F)_(macron(T)_(k,i))) $\
    $hat(nu)_(tau)^ell (t_j) <- hat(nu)_(tau)^ell (t_(j-1)) + hat(S)_(j-1) integral_((t_(j-1), t_j)) hat(S)(s-) tilde(nu)_(k+1) (A(macron(T)_(k,i)), s +  macron(T)_(k+1,i), ell, cal(F)_(macron(T)_(k,i))) hat(Lambda)_(k+1)^ell (dif s | cal(F)_(macron(T)_(k,i))) $ #d \
    else: #i \
    $hat(nu)_(tau)^a (t_j) <- hat(nu)_(tau)^a (t_j) <- 0$ #d \
    $hat(nu)_(tau) (t_j) <- hat(nu)_( tau)^y (t_j) + hat(nu)_(tau)^a (t_j) + hat(nu)_(tau)^ell (t_j) $ \
    $hat(M)^c (t_j) <- bb(1) {macron(Delta)_i = c, macron(T)_(k+1,i) - macron(T)_(k,i) <= t_j} - hat(Lambda)_(k+1)^c (t_j | cal(F)_(macron(T)_(k,i)))$ \
    $hat(S)^c (t_j) <- product_(v in (0, t_j]) (1 - hat(Lambda)_(k+1)^c (dif v | cal(F)_(macron(T)_(k,i))))$ #d \
    $k_i <- {v | t_v <= tau and macron(T)_(k+1,i) - macron(T)_(k,i)}$ \
    $hat("MG")_i <- sum_(j=1)^(k_i) (hat(nu)_(tau) (t_(j_"max") | cal(F)_(macron(T)_(k,i))) - hat(nu)_(tau) (t_j | cal(F)_(macron(T)_(k,i))) ) 1/(hat(S)^c (t_j) hat(S)_j ) (hat(M)^c (t_j) - hat(M)^c (t_(j-1)))$ #d \
    return $hat("MG")$
]

= Real data application <ref:dataapplication>
How should the methods be applied to real data and what data can we use?

Should we apply the methods to trial data?
In that case, the visitation times may no longer be irregular, and we may have to rederive some of the results.
Another possibility is to simply ignore the fact that the visitation times are regular and apply the methods as they are stated.

We also want to compare with other methods. 
- comparison with LTMLE #citep(<ltmle>).
- or multi-state models
Maybe we can look at the data applications in Kjetil Røyslands papers?

An implementation is given in `ic_calculate.R` and `continuous_time_functions.R`
and a simple run with simulated data can be run in `test_against_rtmle.R`.

= Simulation study
The data generating mechanism should be based on real data given in @ref:dataapplication.
Note that the simulation procedure follows the DAG in @fig:simulationdag.
Depending on the results from the data application, we should consider:
- machine learning methods if misspecification of the outcome model appears to be an issue
   with parametric models. If this is indeed the case, we want to apply
   the targeted learning framework and machine learning models for the estimation of the
   nuisance parameters. 
- performance comparison with LTMLE/other methods. 

= Discussion

There is one main issue with the method that we have not discussed yet:
In the case of irregular data, we may have few people with many events.
For example there may only be 5 people in the data with a censoring event as their 4'th event.
In that case, we can hardly estimate $lambda_4^c (dot | history(3))$ based on the data set with observations only for the 4'th event. 
One immediate possibility is to only use flexible machine learning models for the effective parts of the data that have a sufficiently large sample size
and to use (simple) parametric models for the parts of the data that have a small sample size. By using cross-fitting/sample-splitting for this data-adaptive procedure, we will be able to ensure that the
asymptotics are still valid.
Another possibility is to only consider the $k$ first (non-terminal) events in the definition of the target parameter.
In that case, $k$ will have to be specified prior to the analysis which may be a point of contention (otherwise we would have to use a data-adaptive target parameter (@hubbard2016statistical)).
Another possibility is to use IPW at some cutoff point with parametric models; and ignore contributions
in the efficient influence function since very few people will contribute to those terms. 

Let us discuss a pooling approach to handle the issue with few events. We consider parametric maximum likelihood estimation for the cumulative cause specific censoring-hazard $Lambda_(theta_k)^c$ of the $k$'th event. 
Pooling is that we use the model $Lambda_(theta_j)^c = Lambda_(theta^*)^c$ for all $j in S subset.eq {1, dots, K}$ and $theta^* in Theta^*$
which is variationally independent of the parameter spaces $theta_k in Theta_k$ for $k in.not S$.
This is directly suggested by the point process likelihood, which we can write as
$
    &product_(i=1)^n prodint(t, 0, tau_"max") (d Lambda_theta^c (t | cal(F)_(t-)^(i)  )^(Delta N_i^c (t)) (1 - d Lambda_theta^c (t |  cal(F)_(t-)^(i))^(1 - Delta N_i^c (t)) \
        &=product_(i=1)^n (product_(k=1)^(K_i (tau)) d Lambda_(theta_k)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)}) Lambda_(theta_k)^c (t | cal(F)_(T^i_((k-1))))) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((K_i))^i,tau)}) Lambda_(theta_(K_i+1))^c (t | cal(F)_(T^i_((K_i)))))) \
        &=product_(i=1)^n (product_(k in S, k <= K_i (tau) + 1) (d Lambda_(theta^*)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta^*)^c (t | cal(F)_(T^i_((k-1)))))) \
        &qquad times product_(i=1)^n (product_(k in.not S, k <= K_i (tau) + 1) (d Lambda_(theta_k)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta_k)^c (t | cal(F)_(T^i_((k-1)))))) 
$
(Note that we take $T_(K_i + 1)^i = tau_"max"$).
Thus
$
    &op("argmax")_(theta^* in Theta^*) product_(i=1)^n prodint(t, 0, tau_"max") (d Lambda_theta^c (t | cal(F)_(t-)^(i)  )^(Delta N_i^c (t)) (1 - d Lambda_theta^c (t |  cal(F)_(t-)^(i))^(1 - Delta N_i^c (t)) \
        &=op("argmax")_(theta^* in Theta^*) product_(i=1)^n  (product_(k in S, k <= K_i (tau)+1) (d Lambda_(theta^*)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta^*)^c (t | cal(F)_(T^i_((k-1)))))) \
        &qquad times product_(i=1)^n (product_(k in.not S, k <= K_i (tau) +1) (d Lambda_(theta_k)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta_k)^c (t | cal(F)_(T^i_((k-1))))))
$
and that
$
    &op("argmax")_(theta^* in Theta^*) product_(i=1)^n  (product_(k in S, k <= K_i (tau)+1) (d Lambda_(theta^*)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta^*)^c (t | cal(F)_(T^i_((k-1)))))) \
        &=op("argmax")_(theta^* in Theta^*) (product_(k in S) product_(i=1)^n (d Lambda_(theta^*)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k < K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta^*)^c (t | cal(F)_(T^i_((k-1)))))) \
$
So we see that the maximization problem corresponds exactly to finding the maximum likelihood estimator on a pooled data set!
One may then apply a flexible method based on the likelihood, e.g., HAL
to say a model that pools across all time points. One may then proceed greedily,
using Donsker-class conditions, computing the validation based error of a model (likelihood)
that pools across all event points except one. If the second model then
performs better within some margin, we accept the new model and compare
that with a model that pools all events points except two.
Theory may be based on Theorem 1 of @schuler2023lassoedtreeboosting.
In the machine learning literature, this is deemed
"early stopping". 

Other methods provide means of estimating the cumulative intensity $Lambda^x$ directly instead of splitting it up into $K$ separate parameters
using the event-specific cause-specific cumulative hazard functions.
There exist only a few methods for estimating the cumulative intensity $Lambda^x$ directly (see @liguoriModelingEventsInteractions2023 for neural network-based methods and
@weissForestBasedPointProcess2013 for a forest-based method).
Others choices include flexible parametric models/highly adaptive LASSO
using piece-wise constant intensity models and the likelihood is based on Poisson regression.

Alternatively, we can use temporal difference learning to avoid iterative estimation of $Qbar(k)$ altogether (@shirakawaLongitudinalTargetedMinimum2024).

One other direction is to use Bayesian methods. Bayesian methods may be particular useful for this problem since they do not have issues with finite sample size.
They are also an excellent alternative to frequentist Monte Carlo methods for estimating the target parameter with @eq:cuminc
because they offer uncertainty quantification directly through simulating the posterior distribution
whereas frequentist simulation methods do not.

We also note that an iterative pseudo-value regression-based approach (@andersen2003pseudovalue) may also possible, but is
not further pursued in this article due to the computation time of the resulting procedure. Our ICE IPCW estimator
also allows us to handle the case where the censoring distribution depends on time-varying covariates.
//  However, nonparametric Bayesian methods are not (yet) able to deal with a large number of covariates.
// == Data-adaptive choice of $K$

// In practice, we will want to use $K_tau$ to be equal to 1 + maximum number of non-terminal events up to $tau$ in the sample. 
// It turns out, under the boundedness condition of the number of events,
// that an estimator that is asymptotically linear with efficient influence function $phi_tau^*(P) (max_i kappa_i (tau))$
// is also asymptotically linear with efficient influence function $phi_tau^*(P) (K_tau)$
// where $K_tau$ is the last event point such that $P(kappa_i (tau) = K_tau) > 0$.

// Sketch: We want to use $K = K_n = max_i kappa_i (tau)$.
// If we can do asymptotically and efficient inference for $K_n$, then we can also do it for a limiting $K_n <= K$.
// Assume that the estimator is asymptotically linear with efficient influence function $phi_tau^*(P) (K_n)$.
// Then by Assumption 1, there exists a $K_lim$ which is the last point such that $P(K_n = K_lim) > 0$.
// Then, $K_n$ converges to $K_lim$ (by independence), and moreover, under standard regularity conditions such as strict positivity,
// $
//     (bb(P)_n-P) ( phi_tau^*(P) (K_n) - phi_tau^*(P) (K))
// $ is $o_P(n^(-1/2))$, so if have asymptotic linearity in terms of $phi_tau^*(P) (K_n)$, then we automatically have it
// for the original estimator for $phi_tau^*(P) (K_lim)$.
// Proof: $P(K_"lim" - K_n > epsilon) = P(K_"lim" - epsilon > K_n) =  P(K_"lim" - epsilon > K_i (tau))^n -> 0 $.
// Then note that the truncated parameter converges to the non-truncated one by dominated convergence. 

A potential other issue with the estimation of the nuisance parameters are that the history is high dimensional.
This may yield issues with regression-based methods. If we adopt a TMLE approach, we may be able to use collaborative TMLE (@van2010collaborative)
to deal with the high dimensionality of the history.

There is also the possibility for functional efficient estimation using the entire interventional cumulative incidence curve
as our target parameter. There exist some methods for baseline interventions in survival analysis
(@onesteptmle @westling2024inference).

#bibliography("references/ref.bib",style: "apa")

= Appendix

== Finite dimensional distributions and compensators <appendix:fidi>

    Let $(tilde(X)(t))_(t >= 0)$ be a $d$-dimensional càdlàg jump process,
    where each component $i$ is two-dimensional such that $tilde(X)_i (t) = (N_i (t), X_i (t))$
    and $N_i (t)$ is the counting process for the measurements of
    the $i$'th component $X_i (t)$ such that $Delta X_i (t) != 0$ only if $Delta N_i (t) != 0$
and $X (t) in cal(X)$ for some Euclidean space $cal(X) subset.eq RR^(m)$.
    Assume that the counting processes $N_i$ with probability 1 have no simultaneous jumps and that the number of event times is bounded by a finite constant $K < oo$.
Furthermore, let $cal(F)_t = sigma(tilde(X)(s) | s <= t) or sigma(W) in cal(W) subset.eq RR^w$ be the natural filtration.
Let $T_k$ be the $k$'th jump time of $t mapsto tilde(X) (t)$
and let a random measure on $RR_+ times cal(X)$
be given by
    $
        N (d (t, x)) = sum_(k : event(k) < oo) delta_((event(k), X(event(k)))) (d (t, x)).
    $
    Let $cal(F)_(T_((k)))$ be the stopping time $sigma$-algebra associated with
the $k$'th event time of the process $tilde(X)$.
Furthermore, let $status(k) = j$ if $Delta N_j (event(k)) != 0$ and let $bb(F)_k = cal(W) times (RR_+ times {1, dots, d} times cal(X))^k$.


#theorem("Finite-dimensional distributions")[
    Under the stated conditions of this section:
    
    (i).  We have $history(k) = sigma( event(k), status(k), X(event(k))) or history(k-1)$
    and $history(0) = sigma(W)$. Furthermore, $cal(F)^(macron(N))_t = sigma(macron(N) ((0, s], dot) | s <= t) or sigma(W) = cal(F)_t$,
    where
    $
        macron(N) (dif (t, m, x)) = sum_(k:event(k)<oo) delta_((event(k), status(k), X(event(k)))) (d (t,m,x)).
    $
    We refer to $macron(N)$ as the _associated_ random measure. 
    
    (ii). There exist stochastic kernels $Lambda_(k, i)$ from $bb(F)_(k-1)$ to $RR$ and $zeta_(k,i)$ from $RR_+ times bb(F)_(k-1)$ to $RR_+$ such that the compensator for $N$ is given by,
       $
           Lambda (dif (t, m, x)) = sum_(k : event(k) < oo) bb(1) {event(k-1) < t <= event(k)} sum_(i=1)^d delta_i (d m) zeta_(k,i) (d x, t, history(k-1)) Lambda_(k,i) (d t, history(k-1)) product_(l != j) delta_((X_l (event(k-1)))) (d x_l) 
       $
       Here $Lambda_(k, i)$ is the cause-specific hazard measure for $k$'th event of the $i$'th type,
    and $zeta_(k,i)$ is the conditional distribution of $X_i (event(k))$ given $history(k-1)$, $event(k)$ and $status(k) = i$.

    // (iii). The distribution of $history(n)$ is given by
    //    $
    //       &F_n (d w, d t_1, d delta_1, d x_(11), dots, d x_(1 d), dots, d t_n, d delta_n, d x_(n 1), dots, d x_(n d)) \
    //         &= (product_(i=1)^n bb(1) {t_(i-1) < t_i} prodint2(u, t_(i-1), t_i) (1-sum_(j=1)^d Lambda_(i,j) (d u, f_(i-1))) sum_(j=1)^d delta_j (d delta_i) zeta_(i,j) (d x_(i j), t_i, f_(i-1)) Lambda_(i,j) (d t_i, f_(i-1))) mu (d w),
    //    $
    //    and $f_k = (t_k, d_k, x_k, dots t_1, d_1, x_1, w) in bb(F)_k$ for $n in NN$.
    //    Here $#scale(160%)[$pi$]$ denotes the product integral.
] <thm:jointdensity>
#proof[
    To prove (i), we first note that since the number of events are bounded,
    we have the _minimality_ condition of Theorem 2.5.10 of @last1995marked, so
    the filtration $cal(F)^N_t = sigma(N ((0, s], dot) | s <= t) or sigma(W) = cal(F)_t$ where
    $
        N (d (t, tilde(x))) = sum_(k : event(k) < oo) delta_((event(k), tilde(X)(event(k)))) (d (t,tilde(x)))
    $
    Thus $history(k) = sigma (event(k), tilde(X)(event(k))) or history(k-1)$
    and $history(0) = sigma(W)$ in view of Equation (2.2.44) of @last1995marked.
    To get (i), simply note that since the counting proceses do not jump at the same time,
    there is a one-to-one corresponding between $status(k)$ and $N^i (event(k))$ for $i = 1, dots, d$,
    implying that $macron(N)$ generates the same filtration as $N$, i.e., $cal(F)^N_t = cal(F)^(macron(N))_t$ for all $t>=0$.
    
    To prove (ii), simply use Theorem 4.1.11 of @last1995marked which states that
    $
        Lambda(d (t, m, x)) &= sum_(k: event(k) < oo) bb(1) {event(k-1) < t <= event(k)} (P( (event(k), status(k), X (event(k))) in d (t, m, x) | history(k-1))) / P(event(k) >= t | history(k-1))  
    $
    is a $P$-$cal(F)_t$ martingale.
    Then, we find by the "no simultaneous jumps" condition, 
    $
        P(X(event(k)) in d x | history(k-1), event(k) = t, status(k) = j) =  P (X_j (event(k)) in d x_j | history(k-1), event(k) = t, status(k) = j) product_(l != j) delta_((X_l (event(k-1)))) (d x_l)
    $
    We then have,
    $
        &P( (event(k), status(k), X (event(k))) in d (t, m, x) | history(k-1)) / P(event(k) >= t | history(k-1)) \
            &=sum_(j=1)^d delta_j (d m) P(X(event(k)) in d x | history(k-1), event(k) = t, status(k) = j) P(event(k) in d t, status(k) = j | history(k-1) = f_(k-1)) / P(event(k) >= t | history(k-1) = f_(k-1)).
    $
    Letting
    $
        zeta_(k,j) (d x, t, f_(k-1)) := P (X_j (event(k)) in d x | history(k-1) = f_(k-1), event(k) = t, status(k) = j) \
        Lambda_(k, j) (d t, f_(k-1)) := P(event(k) in d t, status(k) = j | history(k-1) = f_(k-1)) / P(event(k) >= t | history(k-1) = f_(k-1))
    $
    completes the proof of (ii).

    // 3. is simply a straightforward extension of Proposition 1/Theorem 3 of @ryalenPotentialOutcomes
    // or an application of Theorem 8.1.2 of @last1995marked. It also follows from iterative applications of 2. 
]

== Simulating the data 
One classical causal inference perspective requires that we know how the data was generated up to unknown parameters (NPSEM) #citep(<pearlCausalityModelsReasoning2009>).
This approach has only to a small degree been discussed in continous-time causal inference literature (@roeysland2024).
This is initially considered in the uncensored case, but is later extended to the censored case.
For a moment, we ponder how the data was generated given a DAG. The DAG given in the section provides
a useful tool for simulating continuous-time data, but not for drawing causal inference conclusions. 
For the event times, we can draw a figure representing the data generating mechanism which is shown in @fig:dag.
Some, such as @chamapiwa2018application, write down this DAG, but with an arrow from $event(k)$ to $covariate(k)$ and $treat(k)$
instead of displaying a multivariate random variable which they deem the "time-as-confounder" approach
to allow for irregularly measured data (see @fig:simulationdag).
Fundamentally, this arrow would only be meaningful if the event time was known prior to the treatment and covariate value measurements,
which they might not be. This can make sense if the event is scheduled ahead of time, but for, say, a stroke
the time is not measured prior to the event. Because a cause must precede an effect,
this makes the arrow invalid from a philosophical standpoint.
On the other hand, DAGs such as the one in @fig:dag, are not informative about the causal relationships
between the variables are. This issue with simultaneous events is likely what has led to the introduction of local independence graphs (@localindependence)
but is also related to the notion that the treatment times are not predictable (that is knowable just prior to the event) as in @ryalenPotentialOutcomes.

#figure(
    diagram(node-stroke: 0.7pt, node-shape: circle, {
        let (historyprior, inst, historyfuture) = ((1,0), (2.5,0), (4,0))
        let (l0, a0, f1) = ((6, 0), (7, -0.5), (7, 0.5))
        // Define the nodes (variables)
        node(enclose: ((0,-1.5), (4.5,1.5)), // a node spanning multiple centers
            inset: 14pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k > 0$:])
        node(enclose: ((5.5,-1), (8,1)), // a node spanning multiple centers
            inset: 10pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k = 0$:])
        dagnode(historyprior, [$historypast(k - 1)$])
        node(inst, [#text(size:6pt)[$(event(k), status(k), covariate(k), treat(k))$]])
        dagnode(historyfuture, [$historynext(k + 1)$])

        edgemsmcens(historyprior, inst)
        edgemsmcens(inst, historyfuture)
    
        dagnode(l0, [$covariate(0)$])
        dagnode(a0, [$treat(0)$])
        dagnode(f1, [$historynext(1)$])

        edgemsm(l0, a0)
        edgemsmcens(a0, f1)
        edgemsmcens(l0, f1)        
    }),
    caption: [
        A DAG representing the relationships between the variables of $O$.
        The dashed lines indicate multiple edges from the dependencies in the past and into the future.
        //Here $historypast(k)$ is the history up to and including the $k$'th event and $historynext(k)$ is the history after and including the $k$'th event.
    ],
) <fig:dag>

#figure(
    diagram(node-stroke: 0.7pt, node-shape: circle, {
        let (historyprior, timestatus, treatment, covar, historyfuture) = ((1,0), (2.5,0), (3,-1), (3,1), (4,0))
        let (l0, a0, f1) = ((6, 0), (7, -0.5), (7, 0.5))
        // Define the nodes (variables)
        node(enclose: ((0,-1.5), (4.5,1.5)), // a node spanning multiple centers
            inset: 10pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k > 0$:])
        node(enclose: ((5.5,-1), (8,1)), // a node spanning multiple centers
            inset: 10pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k = 0$:])
        dagnode(historyprior, [$historypast(k - 1)$])
        dagnode(timestatus, [#text(size:7pt)[$(event(k), status(k))$]])
        dagnode(covar, [$covariate(k)$])
        dagnode(treatment, [$treat(k)$])
        dagnode(historyfuture, [$historynext(k + 1)$])
        

        edgemsmcens(historyprior, treatment)
        edgemsmcens(historyprior, covar)
        edgemsmcens(historyprior, timestatus)
        edgemsm(timestatus, covar)
        edgemsm(timestatus, treatment)
        edgemsmcens(treatment, historyfuture)
        edgemsmcens(covar, historyfuture)
        edgemsmcens(timestatus, historyfuture)
        
    
        dagnode(l0, [$covariate(0)$])
        dagnode(a0, [$treat(0)$])
        dagnode(f1, [$historynext(1)$])

        edgemsm(l0, a0)
        edgemsmcens(a0, f1)
        edgemsmcens(l0, f1)        
    }),
    caption: [
        A DAG for simulating the data generating mechanism.
        The dashed lines indicate multiple edges from the dependencies in the past and into the future.
        Here $historypast(k)$ is the history up to and including the $k$'th event and $historynext(k)$ is the history after and including the $k$'th event.
    ],
) <fig:simulationdag>

== Comparison with the EIF in @rytgaardContinuoustimeTargetedMinimum2022
Let
$
    B_(k-1) (u) = (Qbar(k-1)(tau) -Qbar(k-1)(u)) 1/(tilde(S)^c (u) S (u))
$
We claim that the efficient influence function can also be written as:
$
    phi_tau^*(P) &= sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), j-1)))^(bb(1) (status(j) = a)) (bb(1) (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) dif s)) [ \
        &integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (dif a_k)- B_(k-1) (u)) M_k^(a) (d u) \
         &+integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] - B_(k-1) (u)) M_k^(ell) (d u) \
         &+integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) (1 - B_(k-1) (u)) M_k^(y) (d u) +integral_(event(k-1))^tau 1/(S^c (u | history(k-1)))(0 - B_(k-1) (u)) M_k^(d) (d u) \
        &+  1/(S^c (event(k) | history(k-1))) bb(1) (event(k) <= tau, status(k) = ell, k < K)( Qbar(k) (covariate(k), treat(k-1), event(k), ell, history(k-1)) \
                            &#h(1.5cm) - mean(P) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = event(k) , status(k) = ell, history(k-1)] )]\
                        &+ integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (dif a)- Psi_tau^g (P) 
$

We find immediately that

$
    phi_tau^*(P) &= sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), j-1)))^(bb(1) (status(j) = a)) (bb(1) (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) dif s)) [ \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (dif a_k)) Lambda_k^(a) (d u) \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) Lambda_k^(ell) (d u) \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (1) Lambda_k^(y) (d u) -integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)))(0) Lambda_k^(d) (d u) \
                & -integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^bullet (dif u) \
        &+ macron(Z)_(k,tau) (event(k), status(k), covariate(k), treat(k), history(k-1)) + integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^c ( d u)] \
                &+ integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (dif a)- Psi_tau^g (P)
$
Now note that 
$
    & integral_(event(k - 1))^tau (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) (N^bullet_k (dif s) -  tilde(Y)_(k - 1) (s) hazard(bullet, dif s, k-1)) \   
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &-Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, dif s, k-1)\
        &+ integral_(event(k-1))^(tau and event(k)) (Qbar(k-1)(u))/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, dif s, k-1)  \
$
Let us calculate the second integral
$
    & Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, dif s, k-1) \
        &= Qbar(k-1)(tau) (1/(S^c (event(k) and tau | history(k-1)) S (event(k) and tau | history(k-1)))-1)
$
where the last line holds by the Duhamel equation (2.6.5)
The first of these integrals is equal to
$
    &integral_(event(k-1))^(tau and event(k)) (Qbar(k+1)(u))/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, dif u, k-1) \
        &= integral_(event(k-1))^(tau and event(k)) [integral_(0)^(u) S(s | history(k-1)) cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (dif a_k) ) \
        &+  integral_(0)^(u) S(s | history(k-1)) cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
            &+  integral_(0)^(u) S(s | history(k-1)) cumhazard(k-1, y, d s)]  \
        &times 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet,dif u, k-1)  \
        &= integral_(event(k-1))^(tau and event(k)) integral_(s)^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) cumhazard(k-1, bullet, dif u) [S(s | history(k-1)) cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (dif a_k) ) \
        &+ S(s | history(k-1)) cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
            &+  S(s | history(k-1)) cumhazard(k-1, y, d s)]
$
Now note that
$
    & integral_(s)^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) cumhazard(k-1, bullet, dif u) \
        &=  1/(S^c (tau and event(k) | history(k-1)) S (tau and event(k) | history(k-1))) - 1/(S^c (s | history(k-1)) S (s | history(k-1)))
$
Setting this into the previous integral, we get
$
    &-integral_(event(k-1))^(tau and event(k))  1/(S^c (s) )  [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (dif a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] \
        &+ 1/(S^c (tau and event(k) | history(k-1)) S (tau and event(k) | history(k-1))) Qbar(k-1) (tau and event(k))
$
Thus, we find
$
    & integral_(event(k - 1))^tau (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) (N^bullet_k (dif s) -  tilde(Y)_(k - 1) (s) hazard(bullet, s, k-1) dif s) \   
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &-Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) dif s \
        &+ integral_(event(k-1))^(tau and event(k)) (Qbar(k-1)(u))/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) dif s \
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &-(Qbar(k-1)(tau) (1/(S^c (event(k) and tau | history(k-1)) S (event(k) and tau | history(k-1))))-1) \
        &-integral_(event(k-1))^(tau and event(k))  1/(S^c (s)  )    [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (dif a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] \
        &+ 1/(S^c (tau and event(k) | history(k-1)) S (tau and event(k) | history(k-1))) Qbar(k-1) (tau and event(k)) \
        &=- integral_(event(k-1))^(tau and event(k))  1/(S^c (s)) [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (dif a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] +Qbar(k-1)(tau) 
$

// Calculate 

// $
//     &integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^c ( d u)  \
//         &=integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^bullet ( d u)  \
//         &- sum_(x=a,ell,d,y) 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^x ( d u)  \
//         &=- integral_(event(k-1))^(tau and event(k))  1/(S^c (s))   hazard(bullet, u, k-1) dif u [ cumhazard(k-1, a, d s)  \
//         & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (dif a_k) ) \
//         &+  cumhazard(k-1, ell, d s)  \
//         & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
//             &+  cumhazard(k-1, y, d s)] +Qbar(k-1)(tau) \
//         &-sum_(x=a,ell,d,y) 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^x ( d u)  \
//         &=- integral_(event(k-1))^(tau and event(k))  1/(S^c (s)) [ cumhazard(k-1, a, d s)  \
//         & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (dif a_k) ) \
//         &+  cumhazard(k-1, ell, d s)  \
//         & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
//             &+  cumhazard(k-1, y, d s)] +Qbar(k-1)(tau) \
//         &-sum_(x=a,ell,d,y) 1/(S^c (u | history(k-1))) (-"bla" (x,u)+B_(k-1) (u) M_k^x ( d u)  \
//             &-sum_(x=a,ell,d,y) 1/(S^c (u | history(k-1))) ("bla" (x,u) M^x_k (d u) \
//                 &= Qbar(k-1)(tau) \
//         &+sum_(x=a,ell,d,y) 1/(S^c (u | history(k-1))) ("bla" (x,u)-B_(k-1) (u) M_k^x ( d u)  \
//     &-sum_(x=a,ell,d,y) 1/(S^c (u | history(k-1))) ("bla" (x,u) N^x_k (d u)
// $
