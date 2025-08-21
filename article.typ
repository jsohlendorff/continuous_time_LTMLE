#import "template/definitions.typ": *
//#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
#import "@preview/colorful-boxes:1.4.3": *
#import "@preview/elsearticle:1.0.0": *

#set footnote(numbering: "*")
#set cite(form: "prose")
#show ref: it => [#text(fill: blue)[#it]]
#show: elsearticle.with(
    title: "A Novel Approach to the Estimation of Causal Effects of Multiple Event Point Interventions in Continuous Time",
    authors: (
        (name: "Johan Sebastian Ohlendorff", corr: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen"),
        (name: "Anders Munch"),
        (name: "Thomas Alexander Gerds"),
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
    ],
    format: "3p"
)

//#set page(margin: (left: 10mm, right: 10mm, top: 25mm, bottom: 30mm))
#show math.equation: set text(9pt)
//#set math.equation(numbering: "(1)")
#show: equate.with(breakable: true, sub-numbering: true)

#show math.equation: it => {
  if it.block and not it.has("label") [
    #counter(math.equation).update(v => v - 1)
    #math.equation(it.body, block: true, numbering: none)#label("")
  ] else {
    it
  }  
}

#show: thmrules.with(qed-symbol: $square$)

= Introduction
Randomized controlled trials (RCTs) are widely regarded as the gold standard for estimating the causal effects of treatments on clinical outcomes.
However, RCTs are often expensive, time-consuming, and in many cases infeasible or unethical to conduct.
As a result, researchers frequently turn to observational data as an alternative.
Even in RCTs, challenges such as treatment noncompliance and time-varying confounding — due to factors like side effects or disease progression — can complicate causal inference.
In such cases, one may be interested in estimating the effects of initiating or adhering to treatment over time
on a medical outcome such as the time to an event of interest.

Marginal structural models (MSMs), introduced by @robins1986, are a widely used approach for estimating causal effects from observational data, particularly in the presence of time-varying confounding and treatment.
MSMs typically require that data be recorded on a discrete time scale, capturing all relevant information available to the clinician at each treatment decision point and for the outcome.

However, many real-world datasets — such as health registries — are collected in continuous time, with patient characteristics updated at irregular, subject-specific times.
These datasets often include detailed, timestamped information on events and biomarkers, such as drug purchases, hospital visits, and laboratory results.
Analyzing data in its native continuous-time form avoids the need for discretization.
This is well known for inducing bias 
due to the introduction of time-varying confounding that is unaccounted for (@ryalen2019additive @discretization2020guerra @kant2025irregular @sun2023role @adams2020impact @sofrygin2019targeted).

In this paper, we consider a longitudinal continuous-time framework similar to that of @rytgaardContinuoustimeTargetedMinimum2022
and @roysland2011martingale.
Like @rytgaardContinuoustimeTargetedMinimum2022, we identify the parameter of interest nonparametrically and focus on estimation and inference through the efficient influence function, yielding nonparametrically locally efficient estimators via a one-step procedure
(@vaart1998 @tsiatis2006semiparametric @bickel1993efficient).

To this end, we propose an inverse probability of censoring iterative conditional expectation (ICE-IPCW) estimator, which, like the iterative regression of @rytgaardContinuoustimeTargetedMinimum2022,
iteratively updates nuisance parameters
by regressing back through the history. Both
methods extend the original discrete-time iterative regression method introduced by @bangandrobins2005.

A key innovation in our method is that these updates are performed by indexing backwards through the number of events rather than through calendar time.
This then allows us to apply simple regression techniques
for the nuisance parameters. 
Moreover, our estimator addresses challenges associated with the high dimensionality of the target parameter by employing inverse probability of censoring weighting (IPCW).
The distinction between event-based and time-based updating is illustrated in @fig:timegridrytgaard and @fig:eventgrid.
To the best of our knowledge, no general estimation procedure has yet been proposed for the components involved in the efficient influence function.
Another advantage of using iterative regressions is that the resulting estimator will be
less sensitive to/near practical positivity violations.

For electronic health records (EHRs), the number of registrations for each patient can be enormous.
However, for finely discretized time grids in discrete time,
it has been demonstrated that inverse probability of treatment weighting (IPW)
estimators become increasingly biased and inefficient as the number of time points increases 
whereas iterative regression methods appear to be less sensitive to this issue (@adams2020impact).
Yet, many existing methods for estimating causal effects in continuous time
apply inverse probability of treatment weighting (IPW)
to identify the target parameter (see e.g., @roeysland2024 @roysland2011martingale).

Continuous-time methods for causal inference in event history analysis have also been explored by @roysland2011martingale and @lok2008.
@roysland2011martingale developed identification criteria using a formal martingale framework based on local independence graphs,
enabling causal effect estimation in continuous time via a change of measure.
We shall likewise employ a change of measure to define the target parameter.
@lok2008 similarly employed a martingale approach but focused on structural nested models to estimate a different type of causal parameter—specifically,
a conditional causal effect. However, such estimands may be more challenging to interpret than marginal causal effects.

In Section @section:setting,
we introduce the setting and notation used throughout the paper.
In Section @section:estimand, we present the estimand of interest and provide the iterative representation of the target parameter.
In Section @section:censoring, we introduce right-censoring, discuss the implications for inference, and present the algorithm for estimation,
as well as example usage.
In Section @section:eif, we use the Gateaux derivative to find the efficient influence function
and present the debiased ICE-IPCW estimator.
In Section @section:simulation we present the results of a simulation study
and in Section @section:dataapplication we apply the method to electronic health records data from the Danish registers.

//A key challenge shared by these approaches is the need to model intensity functions,
//which can be difficult to estimate accurately.
//While methods such as Cox proportional hazards (@cox1972) and Aalen additive hazards (@aalen1980model) are commonly used for modeling intensities,
//they are often inadequate in the presence of time-varying confounding, as they do not naturally account for the full history of time-varying covariates.
//Consequently, summary statistics of covariate history are typically used to approximate the intensity functions.

//In this paper, we propose a simple solution to this issue for settings with a limited number of events.
//Our approach enables the use of existing regression techniques from the survival analysis and point process literature to estimate the necessary intensities, providing a practical and flexible alternative.

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

= Setting and Notation <section:setting>

Let $tauend$ be the end of the observation period.
We will focus on the estimation of the interventional absolute risk in the presence of time-varying confounding at a specified time horizon $tau < tauend$.
We let $(Omega, cal(F), P)$ be a statistical experiment on which all processes
and random variables are defined. 

At baseline,
we record the values of the treatment $treat(0)$ and the time-varying covariates $covariate(0)$
and let $cal(F)_0 = sigma(treat(0), covariate(0))$ be the $sigma$-algebra corresponding
to the baseline information.
It is not a loss of generality to assume that we have two treatment options over time so that $A(t) in {0, 1}$ (e.g., placebo and active treatment),
where $A(t)$ denotes the treatment at time $t>=0$.

The time-varying confounders $L(t)$ at time $t>0$ are assumed
to take values in a finite subset $cal(L) subset RR^m$,
so that $L(t) in cal(L)$ for all $t >= 0$.
We assume that the stochastic processes $(L(t))_(t>=0)$ and $(A(t))_(t>=0)$ are càdlàg (right-continuous with left limits),
jump processes.
Furthermore, we require that the times at which the treatment and covariate values may change 
are dictated entirely by the counting processes $(N^a (t))_(t>=0)$ and $(N^ell (t))_(t>=0)$, respectively
in the sense that $Delta A (t) != 0$ only if $Delta N^a (t) != 0$ and $Delta L (t) != 0$ only if $Delta N^ell (t) != 0$ or $Delta N^a (t) != 0$.
Note that we allow, for practical reasons, some of the covariate values to change at the same time as the treatment values.
This can occur if registrations occur only on a daily level if, for example, a patient visits the doctor,
gets a blood test, and receives a treatment all on the same day.
This means that we can practically assume that $Delta N^a Delta N^ell equiv 0$.
We _emphasize_ the importance of the former assumption:
Random changes of covariate values $L$ and treatment $A$ may only happen at a possibly random discrete set of time points.
For technical reasons and ease of notation, we shall assume that the number of jumps at time $tauend$
for the processes $L$ and $A$ satisfies $N^a (tauend)+ N^ell (tauend) <= K - 1$ $P$-a.s. for some $K >= 1$

We have a counting process representing the event of interest $(N^y (t))_(t>=0)$ and the competing event $(N^d (t))_(t>=0)$.

Thus, we have observations from a jump process $alpha(t) = (N^a (t), A (t), N^ell (t), L(t), N^y (t), N^d (t))$,
and the natural filtration $(cal(F)_t)_(t>=0)$ is given by $cal(F)_t = sigma (alpha(s) | s <= t) or cal(F)_0$.
Let $event(k)$ be the $k$'th ordered jump time of $alpha$, that is $T_0 = 0$ and $event(k) = inf {t > event(k-1) | alpha (t) != alpha (event(k-1))} in [0, oo]$ be the time of the $k$'th event
and let $status(k) in {c, y, d, a, ell}$ be the status of the $k$'th event, i.e., $status(k) = x$ if $Delta N^x (event(k)) = 1$.
We let $event(k+1) = oo$ if $event(k) = oo$ or $status(k-1) in {y, d, c}$.
As is common in the point process literature, we define $status(k) = Ø$
if $event(k) = oo$ or $status(k-1) in {y, d,c }$ for the empty mark. 

//We also impose the condition that the last event has to be a terminal event, i.e., $status(K) = y$ or $d$.
We let $treat(k)$ ($covariate(k)$) be the treatment (covariate values) at the $k$'th event. //, i.e., $treat(k) = treat(k-1)$ if $status(k) = ell$.
If $event(k-1) = oo$, $status(k-1) in {y, d, c}$, or $status(k) in {y, d, c}$, we let $treat(k) = Ø$ and $covariate(k) = Ø$.
To the process $(alpha(t))_(t>=0)$, we associate the corresponding random measure $N^alpha$ on $(RR_+ times ({a, ell, y, d, c} times {0,1} times cal(L)))$ by

$
    N^alpha (dif (t, x, a, ell)) = sum_(k: event(k) < oo) delta_((event(k), status(k), treat(k), covariate(k))) (d (t, x, a, ell)),
$
where $delta_x$ denotes the Dirac measure on $(RR_+ times ({a, ell, y, d, c} times {0,1} times cal(L)))$.
It follows that the filtration $(cal(F)_t)_(t>=0)$ is the natural filtration of the random measure $N^alpha$.
Thus, the random measure $N^alpha$ carries the same information as the stochastic process $(alpha(t))_(t>=0)$.
This will be critical for dealing with right-censoring.

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
and its conversion to wide format in @fig:longitudinaldatawide.

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

#figure(
    table(
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
        and are presented in a long format. //Technically, though, events at baseline are not to be considered events, but we include them here for completeness.
    ]
) <fig:longitudinaldatalong>

#figure(
    table(
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
This is needed to ensure the existence of compensators which can be explicitly written via by the regular conditional distributions of the jump times and marks,
but also to ensure that $history(k) = sigma(event(k), status(k), treat(k-1), covariate(k-1)) or history(k-1)$
and $cal(F)_0 = sigma(treat(0), covariate(0))$, where
$history(k)$ stopping time $sigma$-algebra $history(k)$ -- representing the information up to and including the $k$'th event -- associated with
stopping time $event(k)$.
We will interpret $history(k)$ as a random variable instead of a $sigma$-algebra, whenever it is convenient to do so and also make the implicit assumption that whenever we condition on $history(k)$,
we only consider the cases where $event(k) < oo$ and $status(k) in {a, ell}$.

Let $densitytrt(t, k)$ be the probability of being treated at the $k$'th event given $status(k) =a$, $event(k) = t$, $covariate(k)$, and $history(k-1)$.
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

$
    W^g (t) &= product_(k=1)^(N_t) ((densitytrt(event(k), k)^(treat(k)) (1-densitytrt(event(k), k))^(1-treat(k))) / (densitytrt(event(k), k)^(treat(k)) (1-densitytrt(event(k), k))^(1-treat(k))))^(bb(1) {status(k) = a}) \
        &quad times (pi^*_0 (covariate(0))^(A(0)) (1-pi^*_0 (covariate(0)))^(1-A(0)))/ (pi_0 (covariate(0))^(A(0)) (1-pi_0 (covariate(0)))^(1-A(0))),
$ <eq:weightprocess>
// Should be N_(t-)?

where $N_t = sum_k bb(1) {event(k) <= t}$ is random variable denoting the number of events up to time $t$.
If we define the measure $P^(G^*)$ by the density, 
$
    (dif P^(G^*))/(dif P) (omega) = W^g (tauend, omega), quad omega in Omega,
$
representing the interventional world in which the doctor assigns treatments according to the probability measure $pi^*_k (event(k), history(k-1))$ for $k = 0, dots, K-1$,
then our target parameter is given by the mean interventional cumulative incidence function at time $tau$,
$
    Psi_tau^(g) (P) = mean(P^(G^*)) [N^y (tau)] =  mean(P) [N^y (tau) W^g (tau)],
$ <eq:identification>
where $N^y (t) = sum_(k=1)^K bb(1) {event(k) <= t, status(k) =y}$.
In our application, $pi_k^*$ may be chosen arbitrarily,
so that, in principle, _stochastic_, _dynamic_, and _static_ treatment regimes
can be considered.
However, for simplicity of presentation, we use the static observation plan $pi^*_0 (covariate(0)) = 1$ and $pi^*_k (event(k), history(k-1)) = 1$ for all $k = 1, dots, K-1$,
and the methods we present can easily be extended to more complex treatment regimes
and contrasts.
Note that alternatively, we can interpret
the target parameter $Psi_tau^(g, K) (P)$ as
the counterfactual cumulative incidence function of the event of interest $y$ at time $tau$,
when the intervention enforces treatment as part of the $K-1$ first events.
Henceforth, we will assume that @eq:identification
causally identifies the estimand of interest.

// Consider the general sequence of events ${(event(k), status(k), treat(k), covariate(k))}_k$
// which is now allowed to include more than $K$ events in total.
// We are then interested in the target parameter given by
// $
//     Phi_tau^(g, K) (P) =  mean(P) [N^y (tau) W^g (tau and event(K-1))],
// $
// Let
// $
//     k^* = cases(inf {k >= 1 | event(k) > tauend or status(k) in {y, d, c}} "if" event(K-1) < oo, oo "else")
// $
// denote the first event number after $K-1$ events that is terminal.
// In case $k^* = oo$, we define $event(k^*) = oo$ and $status(k^*) = Ø$.
// $k^*$ is well-defined if we can exclude the possibility of an
// explosion, i.e., we assume that the number of events
// in $[0, tauend]$ is finite $P$-a.s.
// Defining $O = (covariate(0), treat(0), event(1), status(1), dots, event(K-1), status(K-1), treat(K-1), covariate(K-1), event(k^*), status(k^*))$,
// we see that $Phi_tau^(g, K) (P) = Psi_tau^(g, K) (P)$.

We now present a simple iterated representation of the data target parameter $Psi_tau^g (P)$ in the case with no censoring.
We discuss more thoroughly the implications for inference of this representation, the algorithm for estimation and examples in @section:censoring
where we also deal with right-censoring.

#theorem[
    Let $H_k = (covariate(k), event(k), status(k), treat(k-1), covariate(k-1), event(k-1), status(k-1), dots, treat(0), covariate(0))$ be the history up to and including the $k$'th event,
    but excluding the $k$'th treatment values for $k > 0$. For $k = 0$, let $H_0 = covariate(0)$.
    Let $Qbar(K): (a_k, h_k) mapsto 0$ and recursively define for $k = K-1, dots, 1$,
    $
        Z^a_(k+1, tau) (u) &= bb(1) {event(k+1) <= u, event(k+1) < tau, status(k+1) = ell) Qbar(k+1) (tau, treat(k), H_(k+1)) \
            &qquad+ bb(1) {event(k+1) <= u, event(k+1) < tau, status(k+1) = a) Qbar(k+1) (tau, 1, H_(k+1)) + bb(1) {event(k+1) <= u, status(k+1) = y), 
    $ <def:Z>
    and
    $
        Qbar(k): (u, a_k, h_k) mapsto mean(P) [Z^a_(k+1, tau) (u) | treat(k) = a_k, H_k = h_k], 
    $ <eq:iterative>
    for $u <= tau$.
    Then,
    $
        Psi_tau^g (P) = mean(P) [Qbar(0) (tau, 1, covariate(0))].
    $ <eq:baselineQ>
    
    // Furthermore for $P$-almost all $(a_(k-1), h_(k-1))$,
    // $
    //     Qbar(k-1) (a_(k-1), h_(k-1)) &= P_(k-1,a) (tau | treat(k-1) = a_(k-1), H_(k-1) = h_(k-1))  + P_(k-1,ell) (tau | treat(k-1) = a_(k-1), H_(k-1) = h_(k-1)) \
    //         &qquad+ P_(k-1,y) (tau | treat(k-1) = a_(k-1), H_(k-1) = h_(k-1)),
    // $ <eq:cuminc>
    // where,
    // $
    //     P_(k-1,a) (t | history(k-1)) &= integral_((event(k-1),t)) S_k (s- | history(k-1)) Qbar(k) (1, covariate(k-1), s, a, history(k-1)) cumhazard(k, a, dif s) \
    //     P_(k-1, ell) (t | history(k-1)) &= integral_((event(k-1),t)) S_k (s- | history(k-1)) \
    //         &qquad (mean(P) [Qbar(k) (treat(k-1), covariate(k), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] ) cumhazard(k, ell, dif s) \
    //         P_(k-1, y) (t | history(k-1)) &= integral_((event(k-1),t]) S_k (s- | history(k-1)) cumhazard(k, y, dif s), quad t <= tau.
    // $
    
]<thm:parameter>

#proof[
    The proof is given in the Appendix.
] 

The representation in @thm:parameter has a natural interpretation:
$Qbar(k)$ is the counterfactual probability of the primary event occuring at or before time $tau$
given the history up to and including the $k$'th event (among the people who are at risk of the event before time $tau$ after $k$ events).
@eq:iterative then suggests that we can estimate $Qbar(k-1)$ via $Qbar(k)$
by considering what has happened as the $k$'th event:
For each individual in the sample, we calculate the integrand in @eq:iterative depending on their value of $event(k)$ and $status(k)$,
and apply the treatment regime as specified by $pi_k^*$ if the individuals event is a treatment event.
Then, we regress these values directly on $(treat(k-1), covariate(k-1), event(k-1), status(k-1), dots, treat(0), covariate(0))$
to obtain an estimator of $Qbar(k-1)$.
Throughout, we will use the notation $Qbar(k) (u)$ to denote the value of $Qbar(k) (u, treat(k), H_(k))$
and $Qbar(k)$ to denote $Qbar(k) (tau, treat(k), H_(k))$.

Note that here, we only set the current value of $treatcensored(k)$ to 1,
instead of replacing all prior treatment values with 1. The latter is certainly closer
to the original iterative conditional expectation estimator (@bangandrobins2005), and is mathematically equivalent but computationally more demanding.
This follows from standard properties of the conditional expectation (see e.g., Theorem A3.13 of @last1995marked).

//On the other hand, we do not recommend using @eq:cuminc directly,
//which involves iterative integration, as this method becomes computationally infeasible even for small values of $K$.

//The second representation (@eq:cuminc) is not important to us now,
//but we will use this representation later.

= Censoring <section:censoring>

In this section, we allow for right-censoring. That is, we introduce a right-censoring time $C>0$
at which we stop observing the multivariate jump process
$alpha$. Let $N^c$ be the censoring process
given by $N^c (t) = bb(1) {C <= t}$.

We will introduce the notation necessary to
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
and define the corresponding censoring survival functions $tilde(S)^c (t | historycensored(k-1)) = prodint(s, event(k-1), t) (1 - cumhazardcensored(k, c, dif s))$
and $S (t | history(k-1)) = product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) Lambda_k^x (dif s | history(k-1)))$,
where $product_(s in (0, t])$ is the product integral over the interval $(0, t]$ (@gill1990survey).
//This determines the probability of being observed at time $t$ given the observed history
//up to $historycensored(k-1)$.

== Algorithm for ICE-IPCW Estimator <alg:ipcwice>

In this section, we present an algorithm for the ICE-IPCW estimator and consider its use in a simple data example.
Ideally, the model for iterative regressions should be chosen flexibly, since even with full knowledge of the data-generating mechanism, the true functional form of the regression model
cannot typically be derived in closed form.
Also, the model should also be chosen such that the predictions are $[0,1]$-valued.
Histories are high-dimensional and should probably be reduced to some low-dimensional representation
if many events occur in the sample.

//(note that this approach is valid as a consequence of @thm:ice is that $cumhazard(k, x, dif t)$ for $x = a, ell, d, y$ are identified via the observed data).

Recall that @thm:parameter states that the
target parameter may be identified via iterative regressions.
We suppose that we are given an estimator
of the censoring compensator $hat(Lambda)^c$.
In particular, for $Qbar(k), k = 0, dots, K-1$,
we start the algorithm at $k = K- 1$ by calculating $hat(S)_k^c (eventcensoredi(k)- | treatcensoredi(k-1), H_(k-1,i))
= product_(s in (eventcensoredi(k-1), eventcensoredi(k)-)) (1 - hat(Lambda)_i^c (s))$.
Given an estimator of $Qbar(k+1)$ denoted by $hat(nu)_((k+1), tau)$, we then calculate the pseudo-outcome $hat(Z)^a_(k,i)$ as follows
- If $statuscensoredi(k) = y$, we calculate $hat(Z)^a_(k,i) =1 /(hat(S)_k^c (eventcensoredi(k)- | treatcensoredi(k-1), H_(k-1,i))) bb(1) {eventcensoredi(k) <= tau}$.
- If $statuscensoredi(k) = a$, evaluate $hat(nu)_((k+1), tau) (1, H_(k,i))$ and calculate $hat(Z)^a_(k,i) = 1/ (hat(S)_k^c (eventcensoredi(k)- | treatcensoredi(k-1), H_(k-1,i))) bb(1) {eventcensoredi(k) < tau} hat(nu)_((k+1), tau) (1, macron(H)_(k,i))$.
- If $statuscensoredi(k) = ell$, evaluate $hat(nu)_((k+1), tau) (treatcensoredi(k-1), H_(k,i))$,
  and calculate $hat(Z)^a_(k,i) = 1/(hat(S)_k^c (eventcensoredi(k)- | treatcensoredi(k-1), H_(k-1,i))) bb(1) {eventcensoredi(k) < tau} hat(nu)_((k+1), tau) (treatcensoredi(k-1), macron(H)_(k,i)).$
Then regress $hat(Z)^a_(k,i)$ on $(treatcensoredi(k-1), H_(k-1,i))$
for the observations with with $eventcensoredi(k-1) < tau$ and $statuscensoredi(k-1) in {a, ell}$
to obtain a prediction function $hat(nu)_k$.
Finally, we compute $hat(Psi)_n = 1/n sum_(i=1)^n hat(nu)_(0) (1, L_i (0))$.

We mention how one may obtain an estimator of the censoring
compensator, but this is a wider topic that we will not concern ourselves with here.
We provide a model for the censoring
that can provide estimates of the hazard measure $1/(P(eventcensored(k) >= t | treatcensored(k-1), macron(H)_(k-1))) P(eventcensored(k) in dif t, statuscensored(k) = c | treatcensored(k-1), macron(H)_(k-1))$,
which is always estimable from observed data.
Then, regress $macron(E)_((k),i) = eventcensoredi(k) - eventcensoredi(k-1)$, known as the $k$'th _interarrival_ time,
       with the censoring as the cause of interest
on $(treatcensoredi(k-1), macron(H)_(k-1,i))$ among the patients who are still at risk after $k-1$ events,
that is for $i$ with $macron(Delta)_(k-1,i) in {a, ell}$ if $k > 1$ and otherwise all $i = 1, dots, n$.
This gives an estimator of the cause-specific cumulative hazard function $hat(Lambda)_k^c$.
This then gives an estimator of the compensator as follows
$
    hat(Lambda)_i^c (t) = sum_(k=1)^K bb(1) {eventcensoredi(k-1) < t <= eventcensoredi(k)} hat(Lambda)_k^c (t - eventcensoredi(k-1) | treatcensoredi(k-1), macron(H)_((k-1),i))
$

// In the first step, the modeler wish to alter the history from an intuitive point of view, so that, in
// the history $historycensored(k-1)$, we use the variables $macron(T)_(k-1) - macron(T)_(j)$ for $j <= k-1$
// instead of the variables $macron(T)_(j)$,
// altering the event times in the history to "time since last event" instead of the "event times" 
// (note that we should then remove $macron(T)_(k-1)$ from the history as it is identically zero).
// This makes our regression procedure in step 1 intuitively look like a simple regression procedure at time zero.

// We also need to discuss what models should be used for $Qbar(k)$.
// Note that 
// $
//     bb(1) {event(k) < tau and status(k) in {a,ell}} Qbar(k) =  mean(P^(G^*)) [N^y (tau)  | history(k)] bb(1) {event(k) < tau and status(k) in {a,ell}} 
// $
// We see thus see that we should use a model for $Qbar(k)$ that is able to capture the counterfactual probability of the primary event occuring at or before time $tau$
// given the history up to and including the $k$'th event (among the people who are at risk of the event before time $tau$ after $k$ events).
//Looking at the algorithm, we see that this does not matter as no observations; indicator functions are all zero.
// otherwise we would not have data.

// e.g., E[ h(X, Y) | Y=1] = E[ h(X, 1) | Y=1]

== Consistency of the ICE-IPCW Estimator <section:conditions>

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
Importantly, we have in fact
//#footnote[The fact that the stopped filtration and the filtration generated by the stopped process are the same is not obvious but follows by Theorem 2.2.14 of @last1995marked.Moreover, from this we have $historycensored(k) = cal(F)^(beta)_(event(k) and C and T^e)$ and we may apply Theorem 2.1.14 to the right-hand side of $cal(F)^(beta)_(event(k) and C and T^e)$ to get the desired statement. ],
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
A simple, sufficient condition for this to hold is e.g., that $C perp history(K)$.
Alternatively, we may assume coarsening at random which will imply @eq:indep (e.g., @gill1997coarsening).
Note that if compensator of the (observed) censoring
process is absolutely continuous with respect to the Lebesgue measure,
then 1 of @thm:ice is satisfied.

//@thm:ice
//This is essentially the weakest condition such that the observed data martingales
//actually identify the unobserved hazards and probabilities.

#theorem[
    Assume that the compensator $Lambda^alpha$ of $N^alpha$ with respect to the filtration $cal(F)^beta_t$ is
    also the compensator with respect to the filtration $cal(F)_t$.
    If
    1. $Delta tilde(Lambda)_(k)^c (t | historycensored(k-1)) + sum_x Delta cumhazard(k, x, t) = 1 quad P-"a.s."=> Delta tilde(Lambda)_(k+1)^c (t | history(k-1)) = 1 quad P-"a.s." or sum_x Delta cumhazard(k, x, t) = 1 quad P-"a.s."$.
    2. $tilde(S)^c (t | historycensored(n-1)) > eta$ for all $t in (0, tau]$ and $n in {1, dots, K}$ $P$-a.s. for some $eta > 0$.
    Let
    $
        macron(Z)^a_(k, tau) (u) =
        1/(tilde(S)^c (eventcensored(k) - | treatcensored(k-1), macron(H)_(k-1))) &(bb(1) {eventcensored(k) <= u,eventcensored(k) < tau, statuscensored(k) = a}
        Qbar(k) (1, macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, eventcensored(k) < tau, statuscensored(k) = ell} Qbar(k) (treatcensored(k), macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, statuscensored(k) = y})
    $
    Then,
    $
        Qbar(k) (u, a_k, h_k) = mean(P) [macron(Z)^a_(k+1, tau) (u) | treatcensored(k) = a_k, macron(H)_(k) = h_k],
    $ <eq:ipcw>
    and hence $Psi_tau^g (P)$ is identifiable from the observed data, where i.e., $macron(H)_k = (covariatecensored(k), treatcensored(k-1), eventcensored(k-1), statuscensored(k-1), dots, treat(0), covariate(0))$.

] <thm:ice>

#proof[
    Proof is given in the Appendix.
]

= Efficient inference <section:eif>

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
To achieve this, we debias our initial ICE-IPCW estimator through double/debiased machine learning (@chernozhukovDoubleMachineLearning2018),
obtaining a one-step estimator for given estimators of the nuisance parameters
appearing in the efficient influence function,
$
    hat(Psi)_n = hat(Psi)^0_n + bb(P)_n phi_tau^* (dot; hat(eta)).
$
Under certain regularity conditions, this estimator is asymptotically linear at $P$ with influence function $phi_tau^* (dot; P)$.
These conditions are not considered in the present paper.

We derive the efficient influence function using the iterative representation given
in @eq:ipcw, working under the conclusions of @thm:ice, by finding the Gateaux derivative of the target parameter.
Note that this does not constitute a rigorous proof that @eq:eif
is the efficient influence function, but rather a heuristic argument.

We note the close resemblance of @eq:eif to the well-known efficient influence function
for the discrete time case which was established in @bangandrobins2005,
with the most notable difference being the presence of the martingale term $tilde(M)^c (dif u)$ in @eq:eif.

A key feature of our approach is that the efficient influence function is expressed in terms of the martingale for the censoring process.
This representation is often computationally simpler, as it avoids the need to estimate multiple martingale terms, unlike the approach of @rytgaardContinuoustimeTargetedMinimum2022.
For a detailed comparison, we refer the reader to the appendix, where we show that our efficient influence function
simplifies to the same as the one derived by @rytgaardContinuoustimeTargetedMinimum2022 in the setting with no competing events.

Of separate interest is @thm:adaptive which shows that
we can adaptively select $K$ based on the observed data.
For instance, we may pick $k=K$ such that $k$ is the largest integer such that
there are at least 40 observations fulfilling that $eventcensored(k-1) < tau$.
Doing so will ensure that we will not have to estimate the terms in @eq:eif
and the corresponding iterative regressions for which there is very little data.
Therefore, our target parameter is instead
$
    Psi_tau^(g, K^*) (P) = mean(P) [tilde(N)^y (tau) W^g (tau and eventcensored(K^*))].
$
It holds that $Psi_tau^(g, K^*) (P) = Psi_tau^g (P)$ if $K^* = K_"lim"$.
Noting that we can pool the last $K_"lim" - K^*$ events into
a single terminal event, the theory discussed thus far can also be
applied to the target parameter $Psi_tau^(g, K^*) (P)$.

#theorem("Efficient influence function")[
    Let for each $P in cal(M)$, $tilde(Lambda)^c_k (t | historycensored(k-1); P)$ be the corresponding
    cause-specific cumulative hazard function for the observed censoring
    for the $k$'th event. Suppose that there is a universal constant $C > 0$
    such that $tilde(Lambda)^c_k (tauend | historycensored(k-1); P) <= C$ for all $k = 1, dots, K$ and
    every $P in cal(M)$.
    The efficient influence function is then given by
    #text(size: 7.5pt)[$
        phi_tau^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1)))   \
            & times bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} ((macron(Z)^a_(k,tau) (tau)- Qbar(k-1) (tau)) \
                &quad + integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (Qbar(k-1) (tau)-Qbar(k-1) (u)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u))\
            & +  Qbar(0) (tau) - Psi_tau^g (P),
    $<eq:eif>]
    where $tilde(M)^c (t) = tilde(N)^c (t) - tilde(Lambda)^c (t)$. Here $tilde(N)^c (t) = bb(1) {C <= t, T^e > t} = sum_(k=1)^K bb(1) {eventcensored(k) <= t, statuscensored(k) = c}$ is the censoring counting process,
    and $tilde(Lambda)^c (t) = sum_(k=1)^K bb(1) {eventcensored(k-1) < t <= eventcensored(k)} tilde(Lambda)_k^c (t | historycensored(k-1))$ is the cumulative censoring hazard process
    given in @section:censoring.
] <thm:eif>

#proof[
        The proof is given in the Appendix.
        ]

#theorem("Adaptive selection of K")[
    Let $K_(n c) = max_(v : sum_(i=1)^n bb(1) {N_(tau i) (tau) >= v} > c)$
    denote the maximum number of events with at
    least $c$ people at risk.
    Suppose that we have the decomposition of the
    estimator $hat(Psi)_n$, such that
    $
        hat(Psi)_n - Psi_tau^(g, K_(n c)) (P) = (bb(P)_n - P) phi_tau^(*, K_(n c)) (dot; P) + o_P (n^(-1/2)).
    $
    Suppose that there is a number $K_"lim" in bb(N)$, such that $P(N_tau = K_"lim") > 0$,
    but $P(N_(tau) > K_"lim") = 0$.
    Then, the estimator $hat(Psi)_n$ satisfies
    $
        hat(Psi)_n - Psi_tau^(g, K_"lim") (P) = (bb(P)_n - P) phi_tau^(*, K_"lim") (dot; P) + o_P (n^(-1/2)).
    $
] <thm:adaptive>
#proof[
    The proof is given in the Appendix.
]

= Simulation study <section:simulation>

We consider a simulation study to evaluate the performance of our ICE-IPCW estimator
and its debiased version. Overall, the purpose of the simulation study is to
establish that our estimating procedure provides valid inference with varying degrees of confounding.
In the censored setting, we do consider the estimation
of the censoring martingale due to the computational difficulties
with the censoring martingale term and
leave this as a future research topic.
The second overall objective is to compare
with existing methods in causal inference, such as
discrete time methods (@ltmle) and a naive
Cox model which treats deviation as censoring,
not addressing time-varying confounding.
In the censored setting, we also address the choice of nuisance parameter models
for the iterative regressions.

*Simulation scenario:*
We simulate a cohort of patients who initiate treatment at time $t = 0$, denoted by $A(0) = 1$
and who are initially stroke-free, $L(0) = 0$.
All individuals are followed for up to $tauend = 900 "days"$ or until death.
During follow-up, patients may experience (at most) one stroke, stop treatment (irreversibly), and die,
that is $N^x (t) <= 1$ for $x = a, ell, y$.
The primary outcome is the _risk of death within $tau = 720$ days_.
We simulate baseline data as $"age" tilde "Unif"(40,90)$,
$L (0) =0$, and $A(0) = 1$.
To simulate the time-varying data, we generate data according to the following intensities
$
    Lambda^(alpha) (dif (t, x, a, ell)) &= bb(1) {t <= T^e and tauend} (delta_(y) (x) lambda^y exp(beta^y_"age" "age" + beta_A^y A(t-) + beta^y_L L(t -)) \
    &quad + bb(1) {N^ell (t -) = 0} delta_(ell) (x) delta_(1) (ell) lambda^ell exp(beta^ell_"age" "age" + beta_A^ell A(t-)) \
        &quad + bb(1) {N^a (t -) = 0} delta_(a) (x) ((1-bb(1) {N^ell (t -) = 0}) gamma_0 exp(gamma_"age" "age") + bb(1) {N^ell (t -) = 0} h_z (t; 360) ) \
        &qquad times (delta_1 (a) pi (t | cal(F)_(t-)) + delta_0 (a) (1 - pi (t |cal(F)_(t-))))),
$ <eq:intensity>
where $h_z (t; 360; 5; epsilon)$ is the hazard function for a 
Normal distribution with mean $360$ and standard deviation $5$,
truncated from some small value $epsilon > 0$
and $pi (t | cal(F)_(t-)) = "expit" (alpha_0 + alpha_"age" "age" + alpha_L L(t-))$
is the treatment assignment probability.
Our intervention is $pi^* (t | cal(F)_(t-)) = 1$
which corresponds to sustained treatment throughout the follow-up period.
Note that @eq:intensity states that the intensities
for $N^ell$ and $N^y$ correspond to multiplicative intensity models.
The case $x=a$ requires a bit more explanation:
The visitation intensity depends on whether the patient has had a stroke or not.
If the patient has not had a stroke, the model specifies
that the patient can be expected to visit the doctor
within 360 days (i.e., the patient is scheduled). If the patient has had a stroke, the visitation intensity
is multiplicative, depending on age, and reflects the fact
that a patient, who has had a stroke, is expected to visit the doctor
within the near future.

In the uncensored setting,
we vary the treatment effect on the outcome
corresponding to $beta^y_A >0$, $beta^y_A = 0$, and $beta^y_A < 0$
and the effect of stroke on the outcome $beta^y_L > 0$, $beta^y_L = 0$, and $beta^y_L < 0$.
We also vary the effect of a stroke on the treatment propensity $alpha_(L)$
and the effect of treatment on stroke $beta_(A)^ell > 0$, $beta_(A)^ell = 0$, and $beta_(A)^ell < 0$.
Furthermore, when applying LTMLE,
we discretize time into 8 intervals (@sec:discretizing-time).
We consider both the debiased ICE estimator and the ICE estimator
without debiasing.
For modeling of the nuisance parameters,
we select a logistic regression model for the treatment propensity
$pi_k (t, history(k-1))$
and a generalized linear model (GLM) with the option `family = quasibinomial()`
for the conditional counterfactual probabilities $Qbar(k)$.
For the LTMLE procedure, we use an undersmoothed LASSO (@lasso) estimator.
Additionally, we vary sample size in the uncensored setting ($n in {100, 2000, 500, 1000}$).
Otherwise, $n=1000$.

For the censored setting, we consider a simulation involving _completely_ independent censoring.
Concretely, the censoring variable is simply generated as $C tilde "Exp"(lambda_c)$
and vary $lambda_c in {0.0002, 0.0005, 0.0008}$.
We consider only two parameter settings for the censoring martingale
as outlined in Figure @table:simulation-parameters.
Finally, three types of models are considered for the estimation of the counterfactual probabilities $Qbar(k)$:
1. A linear model, which is a simple linear regression of the pseudo-outcomes $hat(Z)_k^a$ on the treatment and history variables.
2. A scaled quasibinomial GLM, which is a generalized linear model with the `quasibinomial` as a family argument, where the outcomes are scaled down to $[0, 1]$ by dividing with the largest value of $hat(Z)^a_k$ in the sample.
   Afterwards, the predictions are scaled back up to the original scale by multiplying with the largest value of $hat(Z)^a_k$ in the sample.
3. A tweedie GLM, which is a generalized linear model with the `tweedie` family, where the pseudo-outcomes $hat(Z)_k^a$ may appear marginally as a mixture of a continuous random variable and a point mass at 0.

#set table(
  stroke: (x, y) => if y == 0 {
    (bottom: 0.7pt + black)
  },
    //else if x==0 {
    //(right: 0.1pt + black)
  //},
  align: (x, y) => (
    if x > 0 { center }
    else { left }
  )
)

#figure(
    table(
        columns: (18%, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto),
        inset: 10pt,
        align: horizon,
        table.vline(x: 1),
        [*Parameters*], [$alpha_(0)$], [$alpha_( "age")$], [$alpha_("L")$], [$beta^y_("age")$], [$beta^ell_("age")$], [$beta^y_(A)$], [$beta^ell_(A)$], [$beta^y_("L")$], [$lambda^y$], [$lambda^ell$], [$gamma_"age"$], [$gamma_0$],
        [*Values (varying effects)*], [0.3], [0.02], [*-0.2*, \ #underline[0], \ 0.2], [0.025], [0.015], [*-0.3*, \ 0, \ 0.3], [*-0.2*, \ 0, \ 0.2], [-0.5, \ #underline([0]), \ *0.5*], [0.0001], [0.001], [0], [0.005],
        [*Values (strong confounding)*], [0.3], [0.02], [-0.6, 0.6], [0.025], [0.015], [-0.8, 0.8], [-0.2], [1], [0.0001], [0.001], [0], [0.005],
        [*Values (censoring)*], [0.3], [0.02], [-0.6, 0.6], [0.025], [0.015], [-0.8, 0.8], [-0.2], [1], [0.0001], [0.001], [0], [0.005]
    ),
    caption: [
        Simulation parameters for the simulation study. Each value is varied, holding the others fixed.
        The values with bold font correspond to the values used
        when fixed. The corresponding cases to no effect of time-varying confounders
        are marked with an underline.
    ]) <table:simulation-parameters>

== Results
We present the results of the simulation study in Figure @table:no-time-confounding and Figure @table:strong-time-confounding
in the strong and no time confounding cases, respectively.
In the tables, we report the mean squared error (MSE),
mean bias, standard deviation of the estimates, and the mean of the estimated standard error,
as well as coverage of 95% confidence intervals.
We also present boxplots of the results, showing
bias (Figure @fig:boxplot_results_no_time_confounding, @fig:boxplot_results_strong_time_confounding, @fig:boxplot_results_censored, and @fig:boxplot_censored_ice_ipcw),
as well as standard errors (Figure @fig:se_boxplot_results_no_time_confounding, @fig:se_boxplot_results_strong_time_confounding, and @fig:boxplot_results_censored),
depending on the parameters. Additional results, such as those involving sample size, can be found in the Appendix.

Across all scenarios considered in the uncensored setting (Table @table:no-time-confounding and @table:strong-time-confounding
and Figure @fig:boxplot_results_no_time_confounding, @fig:se_boxplot_results_no_time_confounding, @fig:boxplot_results_strong_time_confounding, and @fig:se_boxplot_results_strong_time_confounding),
it appears that the debiased ICE-IPCW estimator has good performance with respect to bias, coverage, and standard errors.
The debiased ICE-IPCW estimator is unbiased even in settings with substantial time-varying confounding and
consistently matches or outperforms both the naive Cox method and the LTMLE estimator.

Interestingly, when strong time-varying 
confounding is present, LTMLE estimates are biased, but the mean squared errors
are about the same as for the debiased ICE-IPCW estimator.
However, its mean squared error is comparable to that of the debiased ICE-IPCW estimator,
likely owing to the fact that it has generally smaller standard errors.
This reflects a bias–variance trade-off between continuous-time and discrete-time approaches.
The standard errors obtained from
the debiased procedure also appear slightly more biased
than the standard errors obtained from the LTMLE procedure,
but this difference may be negligible.
Note that with our choice of nuisance parameter model
for the iterative regressions that probably is misspecified, we do not encounter
bias in the estimates, but may encounter bias in the standard errors,
as estimation of the standard errors is not doubly robust.

In the presence of right-censoring (Figure @fig:boxplot_results_censored, @fig:se_boxplot_results_censored, and @fig:boxplot_censored_ice_ipcw),
we see that the debiased ICE-IPCW estimator
remains unbiased across all simulation scenarios
and all choices of nuisance parameter models.
Moreover, standard errors are (slightly) conservative
as is to be expected.

With regards to the selection of nuisance parameter models
for the pseudo-outcomes, we find that the linear model provides the most biased estimates for the non-debiased ICE-IPCW estimator
(Figure @fig:boxplot_censored_ice_ipcw), though the differences are not substantial.
In Figure @fig:boxplot_results_censored, we see that for the debiased ICE-IPCW estimator,
there is no substantial difference between the linear, scaled quasibinomial, and tweedie models.
Also note that the Tweedie model produces slightly larger standard errors
for the debiased ICE-IPCW estimator
than the linear or scaled quasibinomial models.
However, the differences are otherwise minor.

#let table_no_time_confounding = csv("simulation_study/tables/results_table_no_time_confounding.csv")
#let _ = table_no_time_confounding.remove(0)

#figure(
table(
    columns: table_no_time_confounding.at(0).len(),
    table.vline(x: 1),
    fill: (_, y) => if ((calc.rem(y, 4) == 0 and y > 0) or (calc.rem(y, 4) == 1)) { gray.lighten(90%) },
        [$beta^y_A$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..table_no_time_confounding.slice(0, 4).flatten(),
    table.hline(),
    ..table_no_time_confounding.slice(4, 8).flatten(),
    table.hline(),
        ..table_no_time_confounding.slice(8, 12).flatten(),
),
    caption: [
        Results for the case without time confounding.
    ]) <table:no-time-confounding>

#let table_strong_time_confounding = csv("simulation_study/tables/results_table_strong_time_confounding.csv")
#let _ = table_strong_time_confounding.remove(0)

#figure(
table(
    columns: table_strong_time_confounding.at(0).len(),
    table.vline(x: 2),
        fill: (_, y) => if ((calc.rem(y, 4) == 0 and y > 0) or (calc.rem(y, 4) == 1)) { gray.lighten(90%) },
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
     [$beta^y_A$], [$alpha_L$], [*Estimator*], [*Coverage*],
     [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..table_strong_time_confounding.slice(0, 4).flatten(),
    table.hline(),
    ..table_strong_time_confounding.slice(4, 8).flatten(),),
        caption: [
                Results for the case with strong time confounding.
        ]) <table:strong-time-confounding>

#figure(
    image("simulation_study/plots/boxplot_results_no_time_confounding.svg"),
        caption: [
                Boxplots of the results for the case without time confounding.
                The lines indicates the true value of the parameter.
        ],
) <fig:boxplot_results_no_time_confounding>

#figure(
    image("simulation_study/plots/se_boxplot_results_no_time_confounding.svg"),
        caption: [
                Boxplots of the standard errors for the case without time confounding.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
) <fig:se_boxplot_results_no_time_confounding>

#figure(
    image("simulation_study/plots/boxplot_results_strong_time_confounding.svg"),
        caption: [
                Boxplots of the results for the case with strong time confounding.
                The lines indicates the true value of the parameter.
        ],
) <fig:boxplot_results_strong_time_confounding>

#figure(
    image("simulation_study/plots/se_boxplot_results_strong_time_confounding.svg"),
        caption: [
                Boxplots of the standard errors for the case with strong time confounding.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
) <fig:se_boxplot_results_strong_time_confounding>

#figure(
    image("simulation_study/plots/boxplot_results_censored.svg"),
        caption: [
                Boxplots of the results for the case with censoring.
            Different degrees of censoring are considered as well different model types for the pseudo-outcomes.
            Only the debiased ICE-IPCW estimator is shown.
        ],
) <fig:boxplot_results_censored>

#figure(
        image("simulation_study/plots/se_boxplot_results_censored.svg"),
                caption: [
                        Boxplots of the standard errors for the case with censoring.
                The red line indicates the empirical standard error of the estimates for each estimator.
                ]) <fig:se_boxplot_results_censored>


#figure(
    image("simulation_study/plots/ice_ipcw_boxplot_results_censored.svg"),
        caption: [
            Boxplots of the results for the case with censoring.
            Different degrees of censoring are considered as well different model types for the pseudo-outcomes.
            Here, the (not debiased) ICE-IPCW estimator is shown.
        ],
) <fig:boxplot_censored_ice_ipcw>

= Application to Danish Registry Data <section:dataapplication>
To illustrate the applicability of our methods,
we applied them to Danish registry data emulating a target trial in diabetes research.
The dataset consisted of $n=20,000$ patients from the Danish registers who
redeemed a prescription for either DPP4 inhibitors or SGLT2 inhibitors between 2012 and 2022.

At baseline (time zero), patients were required to have redeemed such a prescription and
to have an HbA1c measurement recorded prior to their first prescription redemption.
Within our framework, we defined:
- $N^y$ be the counting process for the event of death.
- $N^c$ the counting process for the event of censoring (e.g., end of study period or emigration).
- $N^a$ the counting process counting drug purchases.
- $N^ell$ the counting process for the measurement dates
  at which the HbA1c was measured.
- $L(t)$ denote the (latest) HbA1c measurement at time $t$ and with the baseline HbA1c measurement at time zero (age and sex).
- For each treatment regime (say SGLT2), we defined $A (0) = 1$ if 
  the patient redeemed a prescription for SGLT2 inhibitors first.
  For $t>0$, we defined $A (t) = 1$ if the patient has not purchased DPP4 inhibitors
  prior to time $t$.

Our target parameter is the risk of death,
and we enforce treatment as part of the 20 first events.

For the nuisance parameter estimation, we used a logistic regression model
for the treatment propensity
the `scaled_quasibinomial` option for the conditional counterfactual probabilities $Qbar(k)$.
Censoring was modeled a Cox proportional hazards model using only baseline covariates.
As in the simulation study, we omitted the censoring martingale term,
yielding conservative confidence intervals.

Detailed figures are provided in ? and ??.
For comparison, we also applied the Cheap Subsampling confidence interval (@ohlendorff2025cheapsubsamplingbootstrapconfidence)
to see how robust the confidence intervals provided by our procedure are.
The method was considered since bootstrapping the data is computationally expensive.
With 25 bootstrap repetitions and subsample size $m= 0.8 n$,
we found that the Cheap Subsampling confidence intervals
appear very similar to the ones provided by our debiased ICE estimator
across all time horizons.
Noting the results for the ICE-IPCW estimator (without debiasing),
we see that the ICE-IPCW estimator provides
about the same confidence interval with Cheap Subsampling.
// It is well known (@sofrygin2019targeted) in the discrete-time case that inverse probability weighting (IPW) methods
// are known perform poorly in the presence of many time points.
// Since the number of events is analogous in continuous time is analogous to the number of time points in discrete time,
// this may explain why the confidence intervals appear wider for the ICE-IPCW estimator
// than for the debiased ICE-IPCW estimator, as it has been noted
// that practical positivity violations lead to anti conservative confidence intervals.
// Future work should consider robust inference methods
// with many event points, as this is likely to occur in practice.

= Discussion

In this article, we have presented a new method for causal inference
in continuous-time settings with competing events and censoring.
We have shown that the ICE-IPCW estimator is consistent for the target parameter,
and provided inference for the target parameter using the efficient influence function.
However, we have not addressed the issue of model misspecification,
which is likely to occur in practice.
Two main issues arise from this:
One is that we have not proposed flexible intensity estimation
for both the censoring intensity and the propensity scores.
There exist only a few methods for estimating the cumulative intensity $Lambda^x$ directly (see @liguoriModelingEventsInteractions2023 for neural network-based methods and
@weissForestBasedPointProcess2013 for a forest-based method).
Other choices include flexible parametric models/highly adaptive LASSO
using piecewise constant intensity models where the likelihood is based on Poisson regression.
In principle, machine learning methods can also be applied
to what we have just discussed (Section @alg:ipcwice)
but the effective sample size will be small if we do not pool across time.
Another issue that if we apply a very flexible model
for the censoring distribution,
we will, in theory, need to debias the ICE-IPCW estimator
with the censoring martingale.
Future work should address this issue.

We could have also opted to use a TMLE (@laanTargetedMaximumLikelihood2006) instead
of using a one-step estimator.
This will likely lead to more robust inference
due to instabilities resulting from large inverse probability of treatment weights
A potential other issue with the estimation of the nuisance parameters are that the history is high dimensional
and that the covariates in the history are highly correlated.
This may yield issues with regression-based methods. If we adopt a TMLE approach, we may be able to use collaborative TMLE (@van2010collaborative)
to deal with the high dimensionality of the history.
Another alternative method for inference is to use temporal difference learning to avoid iterative estimation of $Qbar(k)$ altogether (@shirakawaLongitudinalTargetedMinimum2024)
by appropriately extending it to the continuous-time setting.

// One other direction is to use Bayesian methods. Bayesian methods may be particular useful for this problem since they do not have issues with finite sample size.
// They are also an excellent alternative to frequentist Monte Carlo methods for estimating the target parameter,
// because they offer uncertainty quantification directly through simulating the posterior distribution
// whereas frequentist simulation methods do not.

//There is also the possibility for functional efficient estimation using the entire interventional cumulative incidence curve
//as our target parameter. There exist some methods for baseline interventions in survival analysis
//(@onesteptmle @westling2024inference).
// There is one main issue with the method that we have not discussed yet:
// In the case of irregular data, we may have few people with many events.
// For example there may only be 5 people in the data with a censoring event as their 4'th event.
// In that case, we can hardly estimate $lambda_4^c (dot | history(3))$ based on the data set with observations only for the 4'th event. 
// One immediate possibility is to only use flexible machine learning models for the effective parts of the data that have a sufficiently large sample size
// and to use (simple) parametric models for the parts of the data that have a small sample size. By using cross-fitting/sample-splitting for this data-adaptive procedure, we will be able to ensure that the
// asymptotics are still valid.
// Another possibility is to only consider the $k$ first (non-terminal) events in the definition of the target parameter.
// In that case, $k$ will have to be specified prior to the analysis which may be a point of contention (otherwise we would have to use a data-adaptive target parameter (@hubbard2016statistical)).
// Another possibility is to use IPW at some cutoff point with parametric models; and ignore contributions
// in the efficient influence function since very few people will contribute to those terms. 

// Let us discuss a pooling approach to handle the issue with few events. We consider parametric maximum likelihood estimation for the cumulative cause specific censoring-hazard $Lambda_(theta_k)^c$ of the $k$'th event. 
// Pooling is that we use the model $Lambda_(theta_j)^c = Lambda_(theta^*)^c$ for all $j in S subset.eq {1, dots, K}$ and $theta^* in Theta^*$
// which is variationally independent of the parameter spaces $theta_k in Theta_k$ for $k in.not S$.
// This is directly suggested by the point process likelihood, which we can write as
// $
//     &product_(i=1)^n prodint(t, 0, tau_"max") (d Lambda_theta^c (t | cal(F)_(t-)^(i)  )^(Delta N_i^c (t)) (1 - d Lambda_theta^c (t |  cal(F)_(t-)^(i))^(1 - Delta N_i^c (t)) \
//         &=product_(i=1)^n (product_(k=1)^(K_i (tau)) d Lambda_(theta_k)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)}) Lambda_(theta_k)^c (t | cal(F)_(T^i_((k-1))))) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((K_i))^i,tau)}) Lambda_(theta_(K_i+1))^c (t | cal(F)_(T^i_((K_i)))))) \
//         &=product_(i=1)^n (product_(k in S, k <= K_i (tau) + 1) (d Lambda_(theta^*)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta^*)^c (t | cal(F)_(T^i_((k-1)))))) \
//         &qquad times product_(i=1)^n (product_(k in.not S, k <= K_i (tau) + 1) (d Lambda_(theta_k)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta_k)^c (t | cal(F)_(T^i_((k-1)))))) 
// $
// (Note that we take $T_(K_i + 1)^i = tau_"max"$).
// Thus
// $
//     &op("argmax")_(theta^* in Theta^*) product_(i=1)^n prodint(t, 0, tau_"max") (d Lambda_theta^c (t | cal(F)_(t-)^(i)  )^(Delta N_i^c (t)) (1 - d Lambda_theta^c (t |  cal(F)_(t-)^(i))^(1 - Delta N_i^c (t)) \
//         &=op("argmax")_(theta^* in Theta^*) product_(i=1)^n  (product_(k in S, k <= K_i (tau)+1) (d Lambda_(theta^*)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta^*)^c (t | cal(F)_(T^i_((k-1)))))) \
//         &qquad times product_(i=1)^n (product_(k in.not S, k <= K_i (tau) +1) (d Lambda_(theta_k)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta_k)^c (t | cal(F)_(T^i_((k-1))))))
// $
// and that
// $
//     &op("argmax")_(theta^* in Theta^*) product_(i=1)^n  (product_(k in S, k <= K_i (tau)+1) (d Lambda_(theta^*)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k != K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta^*)^c (t | cal(F)_(T^i_((k-1)))))) \
//         &=op("argmax")_(theta^* in Theta^*) (product_(k in S) product_(i=1)^n (d Lambda_(theta^*)^c (T^i_((k)) | cal(F)_(T^i_((k-1)))))^(bb(1) {k < K_i + 1}) prodint(t, 0, tau_"max") (1 - d (bb(1) {t in (T_((k-1))^i,T_((k))^i)})Lambda_(theta^*)^c (t | cal(F)_(T^i_((k-1)))))) \
// $
// So we see that the maximization problem corresponds exactly to finding the maximum likelihood estimator on a pooled data set!
// One may then apply a flexible method based on the likelihood, e.g., HAL
// to say a model that pools across all time points. One may then proceed greedily,
// using Donsker-class conditions, computing the validation based error of a model (likelihood)
// that pools across all event points except one. If the second model then
// performs better within some margin, we accept the new model and compare
// that with a model that pools all events points except two.
// Theory may be based on Theorem 1 of @schuler2023lassoedtreeboosting.
// In the machine learning literature, this is deemed
// "early stopping". 

// Other methods provide means of estimating the cumulative intensity $Lambda^x$ directly instead of splitting it up into $K$ separate parameters
// using the event-specific cause-specific cumulative hazard functions.
// There exist only a few methods for estimating the cumulative intensity $Lambda^x$ directly (see @liguoriModelingEventsInteractions2023 for neural network-based methods and
// @weissForestBasedPointProcess2013 for a forest-based method).
// Others choices include flexible parametric models/highly adaptive LASSO
// using piece-wise constant intensity models and the likelihood is based on Poisson regression.

// We also note that an iterative pseudo-value regression-based approach (@andersen2003pseudovalue) may also possible, but is
// not further pursued in this article due to the computation time of the resulting procedure. Our ICE IPCW estimator
// also allows us to handle the case where the censoring distribution depends on time-varying covariates.
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

//A potential other issue with the estimation of the nuisance parameters are that the history is high dimensional.
//This may yield issues with regression-based methods. If we adopt a TMLE approach, we may be able to use collaborative TMLE (@van2010collaborative)
//to deal with the high dimensionality of the history.

//There is also the possibility for functional efficient estimation using the entire interventional cumulative incidence curve
//as our target parameter. There exist some methods for baseline interventions in survival analysis
//(@onesteptmle @westling2024inference).

#bibliography("references/ref.bib",style: "apa")

= Appendix

== Proof of Theorem 1 <thm:jointdensity>
Let $W_(k, j) = (W^g (event(j))) / (W^g (event(k)))$ for $k < j$ (defining $0/0 = 0$).
    //For brevity of notation, we do not write $bb(1) {event(k-1) < oo and status(k-1) in {a, ell})$.
    We show that 
    $
        Qbar(k) (treat(k), H_k) = mean(P) [sum_(j=k+1)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k), H_k]
    $
    for $k = 0, dots, K - 1$ by backwards induction: // satisfies the desired property of @eq:iterative.

    _Base case_: The case $k = K-1$ is trivial $(W_(K-1,K) bb(1) {event(K) <= tau, status(K) = y} = bb(1) {event(K) <= tau, status(K) = y})$.
    
    _Inductive step_: Assume that the claim holds for $k+1$.
    We find
    $
        &mean(P) [sum_(j=k+1)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k), H_k] \
            &=^(a) mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} W_(k,k+1) \
                &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) in {a, ell}} \
                &#h(1cm) times mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k] | treat(k), H_k) \
            &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} W_(k,k+1) \
                &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = a} \
                &#h(1cm) times mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k] \
                &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = ell} \
                &#h(1cm) times mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k)
                mid(|) treat(k), H_k] \
            &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} \
                &#h(0.5cm) + bb(1) {event(k+1) < tau, status(k+1) = a} \
                &#h(1cm) times mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k] \
                &#h(0.5cm) + bb(1) {event(k+1) < tau, status(k+1) = ell} \
                &#h(1cm) times mean(P) [mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k]
                mid(|) treat(k), H_k) \
            &=^(b) mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} \
                &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = a} \
                &#h(1cm) times mean(P) [W_(k,k+1) Qbar(k+1) (treat(k+1), H_(k+1)) | event(k+1), status(k+1), treat(k), H_k] \
                &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = ell} \
                &#h(1cm) times mean(P) [Qbar(k+1) (treat(k), H_(k+1)) | event(k+1), status(k+1), treat(k), H_k] | treat(k), H_k) \
            &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} \
                &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = a} \
                &#h(1cm) times mean(P) [W_(k,k+1) Qbar(k+1) (treat(k+1), covariate(k), event(k), status(k), treat(k), H_k) | event(k+1), status(k+1), treat(k), H_k] \
                &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = ell} \
                &#h(1cm) times Qbar(k+1) (treat(k), covariate(k+1), event(k), status(k), treat(k), H_k) | treat(k), H_k).
    $
    Repeatedly throughout, we use the law of iterated expectations.
    In a, we use that
    $
        (event(k) <= tau, status(k) = y) subset.eq (event(j) < tau, status(j) in {a, ell})
    $
    for all $j = 1, dots, k-1$ and $k = 1, dots, K$.
    In b, we use the induction hypothesis.
    
    The desired statement about $Qbar(k)$ @eq:iterative now follows from the fact that
    $
        &mean(P) [W_(k-1,k) Qbar(k) (treat(k), H_k) | event(k), status(k) = a, history(k-1)] \
            &= mean(P) [(bb(1) {treat(k) = 1})/(densitytrt(event(k), k)) Qbar(k) (1, H_k) | event(k), status(k) = a, history(k-1)] \
            &= mean(P) [(mean(P) [bb(1) {treat(k) = 1} | event(k), status(k) =a, history(k-1)])/(densitytrt(event(k), k))  Qbar(k) (1, H_k) | event(k), status(k) = a, history(k-1)] \
            &= mean(P) [Qbar(k) (1, H_k) | event(k), status(k) = a, history(k-1)] \
            &= Qbar(k) (1,H_k)
    $ <eq:stepTheorem1>

    A similar calculation shows that $Psi_tau^g (P) = mean(P) [Qbar(0) (1, covariate(0))]$
    and so @eq:baselineQ follows.
    
    // We now show the second statement.
    // Since $cumhazard(k, x, dif t)$ is the cumulative cause-specific hazard given $history(k-1)$ and that the event was of type $x$,
    // it follows that (A5.29 of @last1995marked)
    // $
    //     P ((event(k), status(k)) in d(t,m) | history(k-1)) = sum_(x=a,ell,d,y) delta_x (dif m) prodint2(s, event(k-1), t) (1 - sum_(x = ell, a, d, y) cumhazard(k, x,dif s)) cumhazard(k, z,dif t), 
    // $ <eq:densityProofICE>
    // whenever $event(k-1) < oo$ and $status(k-1) in {a, ell}$, so
    // we get @eq:cuminc by plugging in @eq:densityProofICE to the second last equality of @eq:iterativeProof.

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

== Proof of @thm:ice
We need two lemmas two show this.

#lemma[
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
    and
    $
        bb(1) {statuscensored(n-1) != c} tilde(S) (t | historycensored(n-1)) = bb(1) {statuscensored(n-1) != c} product_(s in (event(k-1),t]) (1 - sum_(x=a,ell,y,d) cumhazard(n, x, dif s) - cumhazardcensored(n, c, dif s)).
    $
] <thm:iceone>
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
    Further supposee that:
    1. $bb(1) {statuscensored(n-1) != c} tilde(S) (t | historycensored(n-1)) = bb(1) {statuscensored(n-1) != c} tilde(S)^c (t | historycensored(n-1)) S (t | history(n-1))$.
    2. $tilde(S)^c (t | historycensored(n-1)) > eta$ for all $t in (0, tau]$ and $n in {1, dots, K}$ $P$-a.s. for some $eta > 0$.

Note that the theorem can now be used to show the consistency of the ICE-IPCW estimator.
We proceed by backwards induction. 
        
$
    & Qbar(k) (tau | historycensored(k)) \
        &= mean(P) [bb(1) {event(k+1) < tau, status(k+1) = a} Qbar(k+1) (1, covariate(k), eventcensored(k+1), status(k+1), history(k)) \
            &#h(1.5cm) + bb(1) {event(k+1) < tau, status(k+1) = ell} Qbar(k+1) (treat(k), covariate(k+1), event(k+1), status(k+1), history(k)) \
            &#h(1.5cm) + bb(1) {event(k+1) <= tau, status(k+1) = y} | history(k) ] \
        &=^(*) mean(P) [bb(1) {event(k+1) < tau, status(k+1) = a} Qbar(k+1) (1, covariate(k), eventcensored(k+1), status(k+1), history(k)) \
            &#h(1.5cm) + bb(1) {event(k+1) < tau, status(k+1) = ell} Qbar(k+1) (treat(k), covariate(k+1), event(k+1), status(k+1), history(k)) \
            &#h(1.5cm) + bb(1) {event(k+1) <= tau, status(k+1) = y} | history(k), cal(C)_k ] \
        &=mean(P) [bb(1) {event(k+1) < tau, status(k+1) = a} Qbar(k+1) (1, covariate(k), eventcensored(k+1), status(k+1), history(k)) \
            &#h(1.5cm) + bb(1) {event(k+1) < tau, status(k+1) = ell} Qbar(k+1) (treat(k), covariate(k+1), event(k+1), status(k+1), history(k)) \
            &#h(1.5cm) + bb(1) {event(k+1) <= tau, status(k+1) = y} | historycensored(k), cal(C)_k ], \
        &= mean(P) [macron(Z)^a_(k) | historycensored(k)] \
$
where $cal(C)_k = (exists.not k : status(k) = c)$.
In $(*)$, we use local independence since the corresponding event lies in the sigma-algebra
$cal(F)_(event(k))^beta$, and so we can use the same mark and conditional event distribution as
in the first line. In the last line, we apply @eq:densitycens
since the conditioning set is a part of $cal(F)_(event(k))^beta$.
    
#lemma[
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
    //First, we argue that for every $t in (0, tau]$ with $tilde(S) (t- | historycensored(k-1)) > 0$ (so dependent on the history), we have
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


== Comparison with the EIF in @rytgaardContinuoustimeTargetedMinimum2022
Let us define in the censored setting
$
    W^g (t) = product_(k = 1)^(tilde(N)_t) (bb(1) {treatcensored(k) = 1}) / (pi_k (eventcensored(k), historycensored(k-1))) (bb(1) {treat(0) = 1}) / (pi_0 (covariate(0))) product_(k=1)^(N_t) (bb(1) {status(k) != c}) / (product_(u in (eventcensored(k-1), eventcensored(k))) (1 - cumhazardcensored(k,c,dif u)))
$
in alignment with @eq:weightprocess.
We verify that our efficient influence function is the same as @rytgaardContinuoustimeTargetedMinimum2022
in the case with absolutely continuous compensators.
For simplicity, we also assume that $covariate(k) = covariate(k-1)$ ($covariatecensored(k) = covariatecensored(k-1)$)
whenever $status(k) = a$ ($statuscensored(k) = a$).
The efficient influence function of @rytgaardContinuoustimeTargetedMinimum2022
is given in Theorem 1 of @rytgaardContinuoustimeTargetedMinimum2022 in our notation by
$ 
    phi_tau^*(P) &= mean(P^(G^*)) [N_y (tau) | cal(F)_0] - Psi_tau (P) \
        &+ integral_0^tau W^g (t -) (mean(P^(G^*)) [N_y (tau) | L(t), N^ell (t), cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | N^ell (t), cal(F)_(t-)]) tilde(N)^ell (dif t) \
        &+ integral_0^tau W^g (t -) (mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 1, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 0, cal(F)_(t-)]) tilde(M)^ell (dif t) \
        &+ integral_0^tau W^g (t -) (mean(P^(G^*)) [N_y (tau) | Delta N^a (t) = 1, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^a (t) = 0, cal(F)_(t-)]) tilde(M)^a (dif t) \
        &+ integral_0^tau W^g (t -) (1 - mean(P^(G^*)) [N_y (tau) | Delta N^y (t) = 0, cal(F)_(t-)]) tilde(M)^y (dif t) \
        &+integral_0^tau W^g (t -) (0 - mean(P^(G^*)) [N_y (tau) | Delta N^d (t) = 0, cal(F)_(t-)]) tilde(M)^d (dif t).
$ <eq:rytgaardeif>
Here, we use $tilde$ to denote that the martingales and counting processes are the observed ones.
We note, for instance, for $x= ell$ that
$
    &mean(P^(G^*)) [N_y (tau) | Delta N^x (t) = 1, cal(F)_(t-)] \
        &=sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)}mean(P^(G^*)) [N_y (tau) | event(k) = t, status(k) = x, history(k-1)] \
        &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} lim_(epsilon -> 0) mean(P^(G^*)) [N_y (tau) | event(k) in (t, t+epsilon), status(k) = x, history(k-1)] \
        &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} lim_(epsilon -> 0) (mean(P^(G^*)) [N_y (tau) bb(1) { event(k) in (t, t+epsilon), status(k) = x} | history(k-1)]) / (mean(P^(G^*)) [bb(1) { event(k) in (t, t+epsilon), status(k) = x} | history(k-1)]) \
        &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} \
        &qquad lim_(epsilon -> 0) (mean(P^(G^*)) [mean(P^(G^*)) [Qbar(k) (tau) | event(k), status(k) = x, history(k-1)] bb(1) {event(k) < tau} bb(1) { event(k) in (t, t+epsilon), status(k) = x} | history(k-1)]) / (mean(P^(G^*)) [bb(1) { event(k) in (t, t+epsilon), status(k) = x} | history(k-1)]) \
        &=^(*) sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} (mean(P) [Qbar(k) (tau) | event(k) =t, status(k) = x, history(k-1)] S (t| history(k-1)) lambda^x_k (t , history(k-1))) /(S (t| history(k-1)) lambda^x_k (t , history(k-1))) \
        &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} mean(P) [Qbar(k) (tau) | event(k) =t, status(k) = x, history(k-1)] \
$ <eq:rytgaardproof1>
where we, in $(*)$, apply dominated convergence.
Similarly, we may find that
$
    mean(P^(G^*)) [N_y (tau) | Delta N^y (t) = 1, cal(F)_(t-)] = 1, \
    mean(P^(G^*)) [N_y (tau) | Delta N^d (t) = 1, cal(F)_(t-)] = 0, \
    mean(P^(G^*)) [N_y (tau) | Delta N^a (t) = 1, cal(F)_(t-)] = sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} Qbar(k) (tau, 1, H_(k))
$ <eq:rytgaardproof2>
For the first term in @eq:rytgaardeif, we find that
$
    &mean(P^(G^*)) [N_y (tau) | L(t), N^ell (t), cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | N^ell (t), cal(F)_(t-)] \
        &= mean(P^(G^*)) [N_y (tau) | L(t), Delta N^ell (t) = 0, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 0, cal(F)_(t-)] \
        &quad +mean(P^(G^*)) [N_y (tau) | L(t), Delta N^ell (t) = 1, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 1, cal(F)_(t-)] \
        &= 0 \
        &quad + sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} (mean(P^(G^*)) [N_y (tau) | L(event(k)), event(k) = t, status(k) = ell, history(k-1)]-mean(P^(G^*)) [N_y (tau) | event(k) = t, status(k) = ell, history(k-1)]) \
        &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} bb(1) (event(k) < tau, status(k) = ell, k < K)  (Qbar(k) (tau) - mean(P) [Qbar(k) (tau) | event(k) = t , status(k) = ell, history(k-1)])
$ <eq:rytgaardproof3>
Next, note that
$
    &mean(P^(G^*)) [N_y (tau) | Delta N^x (t) = 0, cal(F)_(t-)] \
        &=sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} mean(P^(G^*)) [N_y (tau) | (event(k) > t or event(k) = t, status(k) != x), history(k-1)] \
        &=^(**)sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} mean(P^(G^*)) [N_y (tau) | event(k) > t, history(k-1)] \
        &=sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} (mean(P^(G^*)) [N_y (tau) bb(1) { event(k) > t} |history(k-1)])/(mean(P^(G^*)) [bb(1) { event(k) > t } | history(k-1)]) \
        &=sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} (Qbar(k-1) (tau, history(k-1)) - Qbar(k-1) (t, history(k-1)))/(S (t | history(k-1))),
$ <eq:rytgaardproof4>
where in $(**)$, we use that the event $(event(k) = t, status(k) != x)$ has probability zero.
Let $B_(k-1) (u) = (Qbar(k-1)(tau) -Qbar(k-1)(u)) 1/( S (u | historycensored(k-1)))$.
Combining @eq:rytgaardproof1, @eq:rytgaardproof2, @eq:rytgaardproof3, and @eq:rytgaardproof4 with @eq:rytgaardeif, we find that the efficient influence function can also be written as:
$
    phi_tau^*(P) &=(bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1))) bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} \
        &[integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) (Qbar(k) (tau, 1, u, a, historycensored(k-1))- B_(k-1) (u)) tilde(M)^(a) (d u) \
            &quad+integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) (mean(P) [Qbar(k) (tau) | event(k) =u , status(k) = ell, history(k-1)] - B_(k-1) (u)) tilde(M)^(ell) (d u) \
            &quad+integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) (1 - B_(k-1) (u)) tilde(M)^(y) (d u) +integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)))(0 - B_(k-1) (u)) tilde(M)^(d) (d u) \
            &quad+  1/(tilde(S)^c (eventcensored(k) | historycensored(k-1))) bb(1) (eventcensored(k) < tau, statuscensored(k) = ell, k < K) ( Qbar(k) (tau) - mean(P) [Qbar(k) (tau) | eventcensored(k), status(k) = ell, history(k-1)] )]\
        &+ Qbar(0) (tau, 1, covariate(0))- Psi_tau^g (P) \
        &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1))) bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} [ \
            &quad-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) Qbar(k) (1, covariatecensored(k-1), u, a, historycensored(k-1))  lambda^a_k (u , historycensored(k-1)) dif u \
            &quad-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) mean(P) [Qbar(k) (tau) | eventcensored(k) =s , status(k) = ell, historycensored(k-1)] lambda_k^(ell) (u , historycensored(k-1)) dif u \
            &quad-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) (1) lambda_k^(y) (u , historycensored(k-1)) dif u -integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)))(0) lambda_k^(d) (u , historycensored(k-1)) dif u \
            &quad -integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) B_(k-1) (u) M^bullet (dif u) + macron(Z)^a_(k,tau) (tau) + integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) B_(k-1) (u) tilde(M)^c ( d u)] \
        &+ Qbar(0) (tau, 1, covariate(0)) - Psi_tau^g (P),
$ <eq:rytgaard55>
where $M^bullet (t) = sum_(x=a,ell,d,y,c) tilde(M)^x (t)$.
Similarly define $lambda_k^bullet (s , historycensored(k-1)) = sum_(x=a,ell,d,y,c) lambda^x_k (s , historycensored(k-1))$.
Now note that 
$
    & integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) M^bullet (dif u) \
        &=(Qbar(k-1)(tau) - Qbar(k-1)(eventcensored(k))) 1/(tilde(S)^c (eventcensored(k) | historycensored(k-1)) S (eventcensored(k) | historycensored(k-1))) bb(1){eventcensored(k) <= tau} \
        &quad-Qbar(k-1)(tau) integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda_k^bullet (u , historycensored(k-1)) dif u \
            &quad+ integral_(eventcensored(k-1))^(tau and eventcensored(k)) (Qbar(k-1)(u))/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda_k^bullet (u , historycensored(k-1)) dif u \
$ <eq:rytgaard5>
Let us calculate the first integral of @eq:rytgaard5. We have,
$
    & Qbar(k-1)(tau) integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda_k^bullet (u , historycensored(k-1)) dif u = Qbar(k-1)(tau) (1/(tilde(S)^c (eventcensored(k) and tau | historycensored(k-1)) S (eventcensored(k) and tau | historycensored(k-1)))-1)
$ <eq:rytgaard6>
where the last line holds by the Duhamel equation (2.6.5) of @andersenStatisticalModelsBased1993.
The second integral of @eq:rytgaard5 is equal to
$
    &integral_(eventcensored(k-1))^(tau and eventcensored(k)) (Qbar(k-1)(u))/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda_k^bullet (u , historycensored(k-1)) dif u \
        &= integral_(eventcensored(k-1))^(tau and eventcensored(k)) [integral_(0)^(u) S(s | historycensored(k-1)) Qbar(k) (1, covariate(k-1), s, a, historycensored(k-1)) lambda_k^a (s , historycensored(k-1)) dif s \
            &quad +  integral_(0)^(u) S(s | historycensored(k-1)) mean(P) [Qbar(k) (tau) | event(k) =s , status(k) = ell, history(k-1)] lambda_k^ell (s , historycensored(k-1)) dif s \
            &quad +  integral_(0)^(u) S(s | historycensored(k-1)) lambda_k^y (s , historycensored(k-1)) dif s ]  times 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda_k^bullet (u , historycensored(k-1)) dif u \
        &= integral_(eventcensored(k-1))^(tau and eventcensored(k)) integral_(s)^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda_k^bullet (u , historycensored(k-1)) dif u \
        &quad times [ S(s | historycensored(k-1)) Qbar(k) (1, covariate(k-1), s, a, historycensored(k-1)) lambda_k^a (s , historycensored(k-1))  \
            &quad quad +   S(s | historycensored(k-1)) mean(P) [Qbar(k) (tau) | event(k) =s , status(k) = ell, history(k-1)] lambda_k^ell (s , historycensored(k-1))  \
            &quad quad +   S(s | historycensored(k-1)) lambda_k^y (s , historycensored(k-1)) ] dif s \
        &=^(*) 1/(tilde(S)^c (tau and eventcensored(k) | historycensored(k-1)) S (tau and eventcensored(k) | historycensored(k-1))) Qbar(k-1) (tau and eventcensored(k)) \
        &-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/ (tilde(S)^c (s | historycensored(k-1)))  [  Qbar(k) (1, covariate(k-1), s, a, historycensored(k-1)) lambda_k^a (s , historycensored(k-1))  \
            &quad quad +  mean(P) [Qbar(k) (tau) | event(k) =s , status(k) = ell, history(k-1)] lambda_k^ell (s , historycensored(k-1))  \
            &quad quad +  lambda_k^y (s , historycensored(k-1)) ] dif s \
$ <eq:rytgaard7>
In $(*)$, we use that
$
    & integral_(s)^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda^bullet_k (u , historycensored(k-1)) dif u \
        &=  1/(tilde(S)^c (tau and eventcensored(k) | historycensored(k-1)) S (tau and eventcensored(k) | historycensored(k-1))) - 1/(tilde(S)^c (s | historycensored(k-1)) S (s | historycensored(k-1))),
$
which, again, follows by the Duhamel equation.
Thus, we find by @eq:rytgaard5 @eq:rytgaard6, @eq:rytgaard7
$
    & integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) M^bullet (dif u) \
        &=(Qbar(k-1)(tau) - Qbar(k-1)(eventcensored(k))) 1/(tilde(S)^c (eventcensored(k) | historycensored(k-1)) S (eventcensored(k) | historycensored(k-1))) bb(1){eventcensored(k) <= tau} \
        &-Qbar(k-1)(tau) (1/(tilde(S)^c (eventcensored(k) and tau | historycensored(k-1)) S (eventcensored(k) and tau | historycensored(k-1)))-1) \
        &1/(tilde(S)^c (tau and eventcensored(k) | historycensored(k-1)) S (tau and eventcensored(k) | historycensored(k-1))) Qbar(k-1) (tau and eventcensored(k)) \
        &-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/ (tilde(S)^c (s | historycensored(k-1)))  [  Qbar(k) (1, covariate(k-1), s, a, historycensored(k-1)) lambda_k^a (s , historycensored(k-1))  \
            &quad quad +  mean(P) [Qbar(k) (tau) | event(k) =s , status(k) = ell, history(k-1)] lambda_k^ell (s , historycensored(k-1))  \
            &quad quad +  lambda_k^y (s , historycensored(k-1)) ] dif s \
        &=-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/ (tilde(S)^c (s | historycensored(k-1)))  [  Qbar(k) (1, covariate(k-1), s, a, historycensored(k-1)) lambda_k^a (s , historycensored(k-1))  \
            &quad quad +  mean(P) [Qbar(k) (tau) | event(k) =s , status(k) = ell, history(k-1)] lambda_k^ell (s , historycensored(k-1))  \
            &quad quad +  lambda_k^y (s , historycensored(k-1)) ] dif s  +Qbar(k-1)(tau) 
$
This now shows that @eq:rytgaard55 is equal to @eq:eif.

== Proof of @thm:eif

    We let $Qbar(k) (u, a_k, h_k; P)$ denote the right-hand side of @eq:ipcw,
    with $P$ being explicit in the notation and likewise define the notation with $macron(Z)^a_(k, tau) (u; P)$.
    We compute the efficient influence function by calculating the derivative (Gateaux derivative) of $Psi_tau^g (P_epsilon)$
    with $P_epsilon = P + epsilon (delta_(O)-P)$ at $epsilon = 0$,
    where $delta$ denotes the Dirac measure at the point $O$.
    
    First note that:
    $
        &evaluated(partial / (partial epsilon))_(epsilon=0) Lambda_(k, epsilon)^c (dif t | f_(k-1)) \
            &=evaluated(partial / (partial epsilon))_(epsilon=0) (P_epsilon (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P_epsilon (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) \
            &=evaluated(partial / (partial epsilon))_(epsilon=0) (P_epsilon (eventcensored(k) in dif t, statuscensored(k) = c, historycensored(k-1) = f_(k-1))) / (P_epsilon (eventcensored(k) >= t, historycensored(k-1) = f_(k-1))) \
            &= (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) (bb(1) {eventcensored(k) in dif t, statuscensored(k) = c}-P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) \
            &quad- (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) (bb(1) {eventcensored(k) >= t} - P(eventcensored(k) >= t | historycensored(k-1) = f_(k-1)))(P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P (eventcensored(k) >= t| historycensored(k-1) = f_(k-1)))^2 \
            &= (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) (bb(1) {eventcensored(k) in dif t, statuscensored(k) = c}) / (P (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) - bb(1) {eventcensored(k) >= t} (P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P (eventcensored(k) >= t| historycensored(k-1) = f_(k-1)))^2 \
            &= (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) 1/(P (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) (bb(1) {eventcensored(k) in dif t, statuscensored(k) = c} - bb(1) {eventcensored(k) >= t} tilde(Lambda)^c_k (dif t | historycensored(k-1) = f_(k-1))) \
    $
    so that
    $
        &evaluated(partial / (partial epsilon))_(epsilon=0) product_(u in (s, t)) (1- tilde(Lambda)_(k,epsilon)^c (dif t | f_(k-1))) \
            &=evaluated(partial / (partial epsilon))_(epsilon=0) 1/(1-Delta tilde(Lambda)_(k,epsilon)^c (t | f_(k-1)))product_(u in (s, t]) (1- tilde(Lambda)_(k,epsilon)^c (dif t | f_(k-1))) \
            &=^((*))-1/(1-Delta tilde(Lambda)^c_(k,epsilon) (t | f_(k-1))) product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) integral_((s,t]) 1/(1 - Delta tilde(Lambda)_k^c (u |  f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_k (dif u | f_(k-1)) \
            &quad +product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) 1/(1- Delta tilde(Lambda)_k^c (t |f_(k-1)))^2 evaluated(partial / (partial epsilon))_(epsilon=0) Delta tilde(Lambda)_(k,epsilon)^c (t | f_(k-1)) \
            &=-1/(1-Delta tilde(Lambda)^c_(k) (t |f_(k-1))) product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) integral_((s,t)) 1/(1 - Delta tilde(Lambda)_k^c (u | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_k (dif u | f_(k-1)) \
            &quad -1/(1-Delta tilde(Lambda)^c_(k) (t | f_(k-1))) product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) integral_({t}) 1/(1 - Delta tilde(Lambda)_k^c (u | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_k (dif u | f_(k-1)) \
            &quad +product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) 1/(1- Delta tilde(Lambda)_k^c (t | f_(k-1)))^2 evaluated(partial / (partial epsilon))_(epsilon=0) Delta tilde(Lambda)_(k,epsilon)^c (t | f_(k-1)) \
            &=^((**)) -product_(u in (s, t)) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) integral_((s,t)) 1/(1 - Delta tilde(Lambda)_k^c (u | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_(k,epsilon) (dif u |  f_(k-1)).
    $ <eq:derivcumhazard>
    In $(*)$, we use the product rule of differentiation and a result for product integration (Theorem 8 of @gill1990survey), which states that the (Hadamard) derivative of the product integral
    $mu mapsto product_(u in (s, t]) (1 + mu(u))$ in the direction $h$ is given by (for $mu$ of uniformly bounded variation)// it's always finite because; but not necessarily uniformly bounded for all cumhazards; unless we assume that cumhazards themsleves are uniformly bounded.
    $
        &integral_((s,t]) product_(v in (s, u)) (1 + mu(dif v)) product_(v in (u, t]) (1 + mu(dif v)) h(dif u)
            &=product_(v in (s, t]) (1 + mu(dif v)) integral_((s,t]) 1/(1+Delta mu (u)) h(dif u)
    $
    In $(**)$, we use that $integral_({t}) 1/(1 - Delta tilde(Lambda)_k^c (u | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_k (dif u | f_(k-1)) = 1/(1 - Delta tilde(Lambda)_k^c (t | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_(k,epsilon) (t | f_(k-1))$.
    Furthermore, for $P_epsilon = P + epsilon (delta_((X,Y)) - P)$, a simple calculation yields the well-known result
    $
        evaluated(partial / (partial epsilon))_(epsilon=0) mean(P_epsilon) [Y | X = x] = (delta_(X) (x)) / P(X = x) (Y - mean(P) [Y | X = x]).
    $ <eq:derivcondexp>
    Using @eq:ipcw with @eq:derivcondexp and @eq:derivcumhazard, we have
    $
        & evaluated(partial / (partial epsilon))_(epsilon=0) Qbar(k-1) (tau, f_(k-1); P_epsilon) \
            &= delta_(historycensored(k-1) (f_(k-1)))/P(historycensored(k-1) = f_(k-1))  (macron(Z)^a_(k,tau) (tau) - Qbar(k-1) (tau) + \            
                &quad+ integral_(eventcensored(k-1))^(tau) macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) integral_((eventcensored(k-1), t_k)) 1/(1- Delta tilde(Lambda)_k^c (s | f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1))) (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
                &underbrace(#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | f_(k-1)), "A")) \
            &quad+ integral_(eventcensored(k-1))^(tau) (bb(1) {t_k < tau, d_(k) in {a, ell}})/(tilde(S)^c (t_k - | f_(k-1)))  ((bb(1) {a_k = 1}) / (densitytrtcensored(t_(k), k)))^(bb(1) {d_(k) = a}) evaluated(partial / (partial epsilon))_(epsilon=0) lr(Qbar(k) (P_epsilon | a_(k), l_(k),t_(k), d_(k), f_(k-1))) \
            &underbrace(#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | f_(k-1)), "B") 
    $
    for $k=1, dots, K+1$,
    where in the notation with $macron(Z)^a_(k,tau)$, we have made the dependence on $event(k), status(k), treat(k), covariate(k), history(k-1)$ explicit.
    To get B, we use a similar derivation to the one given in Equation @eq:stepTheorem1.
    Now note that for simplifying A, we can write
    $
        &integral_(eventcensored(k-1))^(tau) macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) integral_((eventcensored(k-1),t_k)) 1/(1- Delta tilde(Lambda)_k^c (s | f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
            &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | historycensored(k-1) = f_(k-1)) \
            &= integral_(eventcensored(k-1))^(tau) integral_(s)^tau macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | historycensored(k-1) = f_(k-1)) \
            &#h(1.5cm) 1/(1- Delta tilde(Lambda)_k^c (s | f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
            &= integral_(eventcensored(k-1))^(tau) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
            &#h(1.5cm) 1/(1- Delta tilde(Lambda)_k^c (s | f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
                    &= integral_(eventcensored(k-1))^(tau) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
            &#h(1.5cm) 1/(tilde(S)^c (s | historycensored(k-1) = f_(k-1)) S (s - | historycensored(k-1) = f_(k-1))) (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
    $
    by an exchange of integrals. Here, we apply the result of @thm:ice to get the last equation.
    Hence, we have
    $
        & evaluated(partial / (partial epsilon))_(epsilon=0) Qbar(k-1) (tau, f_(k-1); P_epsilon) \
            &= delta_(historycensored(k-1) (f_(k-1)))/P(historycensored(k-1) = f_(k-1))  (macron(Z)^a_(k,tau) (tau) - Qbar(k-1) (tau) + \            
                &quad+ integral_(eventcensored(k-1))^(tau) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
                &#h(1.5cm) 1/(tilde(S)^c (s | historycensored(k-1) = f_(k-1)) S (s - | historycensored(k-1) = f_(k-1))) (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s))) \
            &quad+ integral_(eventcensored(k-1))^(tau) (bb(1) {t_k < tau, d_(k) in {a, ell}})/(tilde(S)^c (t_k - | f_(k-1)))  ((bb(1) {a_k = 1}) / (densitytrtcensored(t_(k), k)))^(bb(1) {d_(k) = a}) evaluated(partial / (partial epsilon))_(epsilon=0) lr(Qbar(k) (P_epsilon | a_(k), l_(k),t_(k), d_(k), f_(k-1))) \
            &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | f_(k-1)) 
    $ <eq:stepTheorem3>
    Note that for $k=K+1$, the last term vanishes.
    Therefore, we can combine the results from @eq:stepTheorem3 iteratively
    to obtain the result. 

== Proof of @thm:adaptive

We find the following decomposition,
    $
        hat(Psi)_n - Psi_tau^(g, K_"lim") (P) &= hat(Psi)_n - Psi_tau^(g, K_(n c)) (P) + Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P) \
            &= (bb(P)_n - P) phi_tau^(*, K_(n c)) (dot; P)  + Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P) + o_P (n^(-1/2)) \
            &= (bb(P)_n - P) phi_tau^(*, K_"lim") (dot; P) + (bb(P)_n - P) (phi_tau^(*, K_(n c)) (dot; P)- phi_tau^(*, K_"lim") (dot; P)) + Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P) + o_P (n^(-1/2)) \
    $
    We will have shown the result if
    1. $Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P) = o_P (n^(-1/2))$.
    2. $(bb(P)_n - P) (phi_tau^(*, K_(n c)) (dot; P)- phi_tau^(*, K_"lim") (dot; P)) = o_P (n^(-1/2))$ and
    Assume that we have shown that $P(K_(n c) != K_"lim") -> 0$ as $n -> oo$.
    We have that
    $
        sqrt(n) (Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P)) = sqrt(n) bb(1) {K_(n c) != K_"lim"} (Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P)) := E_n
    $
    and
    $
        P(|E_n| > epsilon) <= P(K_(n c) != K_"lim") -> 0,
    $
    as $n -> oo$. A similar conclusion holds for 2.
    We now show that $P(K_(n c) != K_"lim") -> 0$.
    First define that
    $K_n = max_i N_(tau i)$.
    Then, we can certainly write that
    $
         K_(n c) -  K_"lim" = K_(n c) - K_n + K_n - K_"lim",
    $ <eq:Knlim>
    By independence and definition of $K_n$, we have
    $
        P(K_n != K_"lim") = P(K_n < K_"lim") = P(N_tau < K_"lim")^n -> 0
    $
    We now show that $P(K_(n c) < K_n) -> 0$ as $n -> oo$,
    which will show that $P(K_(n c) != K_"lim") -> 0$ as $n -> oo$ by @eq:Knlim.
    We have, 
    $
        P( K_(n c) != K_n) = P( union_(v=1)^(K_"lim") (sum_(i=1)^n bb(1) {N_(tau i) >= v} <= c))
            &<= sum_(v=1)^(K_"lim") P( sum_(i=1)^n bb(1) {N_(tau i) >= v} <= c) -> 0
    $
    as $n -> oo$. Here, we use that
    $
        sum_(i=1)^n bb(1) {N_(tau i) >= v} 
    $
    diverges almost surely to $oo$. Too see this, note that $sum_(i=1)^n bb(1) {N_(tau i) >= v}$ is almost surely monotone
    in $n$, and
    $
        sum_(i=1)^n P(N_(tau i) >= v) = n P(N_tau >= v) -> oo
    $
    From this and Kolmogorov's three series theorem, we conclude that
    $
        sum_(i=1)^n bb(1) {N_(tau i) >= v} -> oo
    $
    almost surely as $n -> oo$
    and that
    $
        sum_(i=1)^n bb(1) {N_(tau i) >= v} <= c
    $
    has probability tending to zero as $n -> oo$ as desired.

== Additional simulation results

=== Uncensored case

==== Varying effects (A on Y, L on Y, A on L, L on A)
#let table_A_on_Y = csv("simulation_study/tables/results_table_vary_effect_A_on_Y.csv")
#let _ = table_A_on_Y.remove(0)

#table(
    columns: table_A_on_Y.at(0).len(),
        table.vline(x: 1),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$beta^y_A$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..table_A_on_Y.slice(0, 4).flatten(),
    table.hline(),
    ..table_A_on_Y.slice(4, 8).flatten(),
        table.hline(),
    ..table_A_on_Y.slice(8, 12).flatten(),
)

#let table_L_on_Y = csv("simulation_study/tables/results_table_vary_effect_L_on_Y.csv")
#let _ = table_L_on_Y.remove(0)

#table(
    columns: table_L_on_Y.at(0).len(),
        table.vline(x: 1),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$beta^y_L$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..table_A_on_Y.slice(0, 4).flatten(),
    table.hline(),
    ..table_A_on_Y.slice(4, 8).flatten(),
        table.hline(),
    ..table_A_on_Y.slice(8, 12).flatten(),
)

#let table_A_on_L = csv("simulation_study/tables/results_table_vary_effect_A_on_L.csv")
#let _ = table_A_on_L.remove(0)

#table(
    columns: table_A_on_L.at(0).len(),
        table.vline(x: 1),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$beta^L_A$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..table_A_on_Y.slice(0, 4).flatten(),
    table.hline(),
    ..table_A_on_Y.slice(4, 8).flatten(),
        table.hline(),
    ..table_A_on_Y.slice(8, 12).flatten(),
)

#let table_L_on_A = csv("simulation_study/tables/results_table_vary_effect_L_on_A.csv")
#let _ = table_L_on_A.remove(0)

#table(
    columns: table_L_on_A.at(0).len(),
    table.vline(x: 1),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$alpha_L$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
        ..table_A_on_Y.slice(0, 4).flatten(),
    table.hline(),
    ..table_A_on_Y.slice(4, 8).flatten(),
        table.hline(),
    ..table_A_on_Y.slice(8, 12).flatten(),
    
)

==== Sample size

#let table_sample_size = csv("simulation_study/tables/results_table_sample_size.csv")
#let _ = table_sample_size.remove(0)

#table(
    columns: table_sample_size.at(0).len(),
    table.vline(x: 1),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$n$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..table_sample_size.slice(0, 2).flatten(),
    table.hline(),
    ..table_sample_size.slice(2, 4).flatten(),
        table.hline(),
    ..table_sample_size.slice(4, 6).flatten(),
    table.hline(),
        ..table_sample_size.slice(6, 8).flatten(),
    
)

=== Censored

#let table_censored = csv("simulation_study/tables/table_censored.csv")
#let _ = table_censored.remove(0)

#table(
    columns: (5%, 5%, 5%, 8%, auto, auto, auto, auto, auto, auto, auto),
    table.vline(x: 4),
      fill: (_, y) => if calc.odd(y) { gray.lighten(90%) },
    //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
    [$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$lambda_c$], [*Model Out.*], [*Estimator*], [*Cov.*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..table_censored.slice(0, 6).flatten(),
    table.hline(),
    ..table_censored.slice(6, 12).flatten(),
    table.hline(),
    ..table_censored.slice(12, 18).flatten(),
    table.hline(),
    ..table_censored.slice(18, 24).flatten(),
    table.hline(),
    ..table_censored.slice(24, 30).flatten(),
    table.hline(),
    ..table_censored.slice(30, 36).flatten(),
)

== Additional boxplots

=== Uncensored case

==== Varying effects (A on Y, L on Y, A on L, L on A)
#figure(
    image("simulation_study/plots/boxplot_results_vary_effect_A_on_Y.svg"),
        caption: [
                Boxplots of the results for the case with varying effect of $A$ on $Y$.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("simulation_study/plots/se_boxplot_results_vary_effect_A_on_Y.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying effect of $A$ on $Y$.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

#figure(
    image("simulation_study/plots/boxplot_results_vary_effect_L_on_Y.svg"),
        caption: [
                Boxplots of the results for the case with varying effect of $L$ on $Y$.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("simulation_study/plots/se_boxplot_results_vary_effect_L_on_Y.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying effect of $L$ on $Y$.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

#figure(
    image("simulation_study/plots/boxplot_results_vary_effect_A_on_L.svg"),
        caption: [
                Boxplots of the results for the case with varying effect of $A$ on $L$.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("simulation_study/plots/se_boxplot_results_vary_effect_A_on_L.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying effect of $A$ on $L$.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

#figure(
    image("simulation_study/plots/boxplot_results_vary_effect_L_on_A.svg"),
        caption: [
                Boxplots of the results for the case with varying effect of $L$ on $A$.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("simulation_study/plots/se_boxplot_results_vary_effect_L_on_A.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying effect of $L$ on $A$.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)


==== Sample size

#figure(
    image("simulation_study/plots/boxplot_results_sample_size.svg"),
        caption: [
                Boxplots of the results for the case with varying sample size.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("simulation_study/plots/se_boxplot_results_sample_size.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying sample size.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

== Discretizing time <sec:discretizing-time>
We briefly illustrate how to discretize the time horizon into $K$ intervals,
with time horizon $tau$, representing the usual longitudinal setting. 
Let $t_k = k times tau / K$ for $k = 1, dots, K$.

Put
$
    Y_k &= N^y (t_k), \
    L_k &= L (t_k), \
    A_k &= A (t_k).
$
Our data set then consists of
$
    O = ("age", covariate(0), treat(0), Y_1, L_1, A_1, dots, Y_(K-1), L_(K-1), A_(K-1), Y_K)
$
