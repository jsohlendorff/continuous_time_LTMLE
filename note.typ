#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
///#import "@preview/cetz:0.3.3"
#import "@preview/cheq:0.2.2": checklist
#import "@preview/algorithmic:1.0.0"
#import algorithmic: algorithm

#set footnote(numbering: "*")
#show: checklist
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

// - [x] Clean up figures.
// - [x] Clean up existence of compensator + integral. 
// - [x] identifiability. My potential outcome approach. Add figure for potential outcome processes.
//       Show full identification formula without reweighting
// - [x] Censoring. Independent censoring IPCW rigorously.
// - [x] Consistency of estimator. Skip not done in other papers.
// - [/] Efficient influence function. Cleanup.
// - [ ] Simulation study (ML?).
// - [ ] Comparison of EIF and target parameter with @rytgaardContinuoustimeTargetedMinimum2022.
// - [ ] Consistency of variance estimator?
// - [/] Debiased estimator
// - [/] DR properties + ML rates/criteria (rate conditions + conditions for $hat(nu)^*$)
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
We establish identification criteria for the causal effect of treatment on an outcome within this setting.
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


// #figure(cetz.canvas(length: 1cm, {
//   import cetz.draw: *

//   set-style(
//             mark: (fill: black, scale: 2),
//             stroke: (thickness: 1pt, cap: "round"),
//             angle: (
//                 radius: 0.3,
//                 label-radius: .8,
//                 fill: green.lighten(80%),
//                 stroke: (paint: green.darken(50%))
//             ),
//             content: (padding: 8pt)
//         )
  
//   let time_grid(cord_start,cord_end, time_values, inc: 0.1, anchor: "north") = {
//       // Main axis line
//       set-style(mark: (end: ">"))
//       line(cord_start, cord_end)
//       set-style(mark: none)

//       // General time line
//       let early_stop = cord_end.first() - 1/10 * cord_end.first()
//       let t_grid = frange(cord_start.first()+inc,early_stop - inc, inc)
      
//       // Start line
//       line((cord_start.first(), -2*inc+cord_start.last()), (cord_start.first(), 2*inc+cord_start.last()), name:"lstart")
//       content("lstart.start", [], anchor: "east")
      
//       // End line
//       line((early_stop - inc, -2*inc+cord_end.last()), (early_stop - inc, 2*inc+cord_end.last()), name: "lend")
//       content("lend.start", [#text(size: 12pt)[$tau_"end"$]],anchor: "north")

//       // Draw grid
//       //for i in t_grid {
//       //  line((i, -inc+cord_start.last()), (i, inc+cord_start.last()))    
//       //}

//       // Deal with the marks/events
//       let event_list = ()
//       for t in range(0, time_values.len()) {
//         event_list.push((name: "v" + str(t), value: time_values.at(t), mformat: $T_( #(t+1) )$))
//       }
//       for v in event_list {
//         line((v.value + cord_start.first(), -2*inc+cord_start.last()), (v.value+cord_start.first(),2*inc+cord_start.last()), name: v.name)
        
//         content(v.name + ".start", [#text(size: 12pt)[#v.mformat]], anchor: anchor)
//       }
//   }
//     for v in (2,4) {
//         line((v, 0.75), (v, 1.25), stroke: red)
//     }
//     // Deal with the marks/events
    
//     let grid2 = (1,1.7, 2.4,2.8)
    
//     group({time_grid((0,1),(5,1), grid2, anchor: "north-east")})
//     set-style(mark: (end: ">", scale: 1))
//     bezier((1,1.25), (2,1.25),(1.5,2.4), stroke: blue)
//     bezier((1.7,0.75), (2,0.75), (1.85,0.25), stroke: blue)
//     bezier((2.4,1.25), (4,1.25), (3,2), stroke: blue)
//         bezier((2.8,0.75), (4,0.75), (3.4,0.25), stroke: blue)
// }), caption:  [The "usual" approach where time is discretized. Each event time and its corresponding mark
//     is rolled forward to the next time grid point, that is the values of the observations are updated based on the
//     on the events occuring in the previous time interval.
// ]) <fig:discretetimegrid>

#figure(timegrid(new_method: false), caption:  [The figure illustrates the sequential regression approach
    given in @rytgaardContinuoustimeTargetedMinimum2022 for two observations:
    Let $t_1 < dots < t_m$ be all the event times in the sample.
    Then, given $mean(Q)[Y | cal(F)_(t_(r))]$,
    we regress back to $mean(Q)[Y | cal(F)_(t_(r-1))]$ (through multiple regressions).
],) <fig:timegridrytgaard>

#figure(timegrid(new_method: true), caption: [The figure illustrates the sequential regression approach
    proposed in this article. For each event $k$ in the sample, we regress back on the history $history(k-1)$.
    That is, given $mean(Q)[Y | history(k)]$,
    we regress back to $mean(Q)[Y | history(k-1)]$.
    In the figure, $k=3$.
],) <fig:eventgrid>

= Setting and Notation

Let $tauend$ be the end of the observation period.
We will focus on the estimation of the interventional absolute risk in the presence of time-varying confounding at a specified time horizon $tau < tauend$.
We let $(Omega, cal(F), P)$ be a probability space on which all processes
and random variables are defined.

// Let $cumhazard(k, x, t)$ be the cumulative hazard of $x$ of the $(k+1)$'th event at time $t$ given the history up to the $k$'th event.
// We focus on estimating $cumhazard(k, x, t)$ for $k = 0, dots, K$ for $K >= 0$ rather than $Lambda^x (t \| cal(F)_(t -))$.
// Here $cal(F)_(T_k)$ is the information up to the $k$'th event -- a so-called stopping time $sigma$-algebra.
//Each of these $sigma$-algebras can be represented by a fixed number of random variables, so that regression can be applied at each event point. 
//We let $pi_0(dot | covariate(0))$ be the density of the baseline treatment given the covariates at time 0
//(with respect to some measure $nu_a$) and
//$mu_0$ be the density of time-varying covariates at time 0 (with respect to some measure $nu_ell$).

At baseline,
we record the values of the treatment $treat(0)$ and the time-varying covariates $covariate(0)$
and let $cal(F)_0 = sigma(treat(0), covariate(0))$ be the $sigma$-algebra corresponding
to the baseline information.
//The time-varying covariates may principally include covariates
//which do not change over time, but for simplicity of notation, we will include them among
//those that do.
We assume that we have two treatment options over time so that $A(t) in {0, 1}$ (e.g., placebo and active treatment),
where $A(t)$ denotes the treatment at time $t>=0$.
The time-varying confounders $L(t)$ at time $t>0$ are assumed
to take values in a finite subset $cal(L) subset RR^m$,
so that $L(t) in cal(L)$ for all $t >= 0$.
We assume that the stochastic processes $(L(t))_(t>=0)$ and $(A(t))_(t>=0)$ are càdlàg (right-continuous with left limits),
jump processes. The fact that they are jump processes by @assumptionbounded means that for $P-$almost all $omega in Omega$,
the processes $L(omega, dot)$ and $A(omega, dot)$ have at most $K-1$ jumps.// #footnote[If this does not hold, then we can view our target parameter as a truncated mean.].//#footnote[The assumption that the number of jumps is bounded can maybe be relaxed to a no explosion condition, but we do not pursue this here.].
//and that $L(t) : Omega -> RR^m$ and $A(t) : Omega -> RR$ are measurable for each $t >= 0$, respectively.
Furthermore, we require that the times at which the treatment and covariate values may change 
are dictated entirely by the counting processes $(N^a (t))_(t>=0)$ and $(N^ell (t))_(t>=0)$, respectively
in the sense that $Delta A (t) != 0$ only if $Delta N^a (t) != 0$ and $Delta L (t) != 0$ only if $Delta N^ell (t) != 0$.
//The jump times of these counting processes
//thus represent visitation times. 

We also have counting processes representing
the event of interest $(N^y (t))_(t>=0)$ and the competing event $(N^d (t))_(t>=0)$.//, and the censoring process $(N^c)_(t>=0)$.
Later, we will introduce the counting process $N^c$ for the censoring process.
//Finally, let $N^c$ be the counting process for the censoring counting process.
For all counting processes involved, we assume for simplicity that the jump times differ with probability 1 (@assumptionnosimultaneous).
//Moreover, we assume that only a bounded number of events occur for each individual in the time interval $[0, tauend]$ (@assumptionbounded).
Thus, we have observations from a the jump process $alpha(t) = (N^a (t), A (t), N^ell (t), L(t), N^y (t), N^d (t))$,
and the natural filtration $(cal(F)_t)_(t>=0)$ is given by $cal(F)_t = sigma (alpha(s) | s <= t) or cal(F)_0$.
Let $event(k)$ be the $k$'th ordered jump time of $alpha$, that is $T_0 = 0$ and $event(k) = inf {t > event(k-1) | alpha (t) != alpha (event(k-1))} in [0, oo]$ be the time of the $k$'th event
and let $status(k) in {y, d, a, ell}$ be the status of the $k$'th event, i.e., $status(k) = x$ if $Delta N^x (event(k)) = 1$, so that

1. each $event(k)$ is a $cal(F)_t$ stopping time.
2. $event(k) < event(k+1)$ if $event(k) < oo$.
3. $event(k+1) = oo$ if $event(k) = oo$ or $status(k-1) in {y, d}$.

//We also impose the condition that the last event has to be a terminal event, i.e., $status(K) = y$ or $d$.
We let $treat(k)$ ($covariate(k)$) be the treatment (covariate values) at the $k$'th event, i.e., $treat(k) = A(event(k))$ if $status(k) = a$ ($covariate(k) = L(event(k))$ if $status(k) = ell$)
and $treat(k) = A(event(k-1))$ ($covariate(k) = L(event(k-1))$) otherwise.
To the process $(alpha(t))_(t>=0)$, we associate the corresponding random measure $N^alpha$ on $(RR_+ times ({y, d, a, ell} times {0,1} times cal(L)))$ by
$
    N^alpha (d (t, x, a, ell)) = sum_(k: event(k) < oo) delta_((event(k), status(k), treat(k), covariate(k))) (d (t, x, a, ell)),
$
where $delta_x$ denotes the Dirac measure on $(RR_+ times ({y, d, a, ell} times {0,1} times cal(L)))$.
It follows that the filtration $(cal(F)_t)_(t>=0)$ is the natural filtration of the random measure $N^alpha$ (@thm:jointdensity (i)).
Thus, the random measure $N^alpha$ carries the same information as the stochastic process $(alpha(t))_(t>=0)$.
This will be critical for identification of the causal effect of interest and dealing with right-censoring.

//Note that also by @assumptionbounded, this means that there exists a compensator $Lambda$ such that
//$
//    N (d (t, x, a, ell)) - Lambda (d (t, x, a, ell))
//$
//is a martingale with respect to the filtration $(cal(F)_t)_(t>=0)$.
// E N_t < oo
//Since the filtration is the natural filtration, it follows that the stopping time

Furthermore, it follows that the stopping time $sigma$-algebra $history(k)$ associated with
stopping time $event(k)$ fulfills that $history(k)= sigma(event(k), status(k), treat(k), covariate(k)) or history(k-1)$. $history(k)$ represents the information up to the $k$'th event.
We will interpret $history(k)$ as a random variable instead of a $sigma$-algebra, whenever it is convenient to do so and also make the implicit assumption that whenever we condition on $history(k)$,
we only consider the cases where $event(k) < oo$ and $status(k) in {a, ell}$.

We observe $O=history(K) = (event(K), status(K), event(K-1), status(K-1), treat(K-1), covariate(K-1), dots, treat(0), covariate(0)) ~ P in cal(M)$ where
$cal(M)$ is the statistical model, i.e., a set of probability measures. 
Let $densitytrt(t, k)$ be the probability of being treated at the $k$'th event given $status(k) =a, event(k) = t$, and $history(k-1)$.
//given that the event time is $t$ and that the $k$'th event is a visitation time
//and let $densitytrtmeasure(t, d a, k)$ be the corresponding probability measure.
Similarly, let $densitycov(t, dot, k)$ be the probability measure for the covariate value $status(k) = ell, event(k) = t$, and $history(k-1)$.
Let also $cumhazard(k, x, dif t)$ be the cumulative cause-specific hazard measure #footnote[Let $T in (0, oo]$ and $X in cal(X)$ be random variables. Then the cause-specific cumulative hazard measure is given by
    $Lambda_x (dif t) = bb(1) {P(T >= t} > 0} P(T in dif t, X = x) / P(T >= t)$ (Appendix A5.3 of @last1995marked).] for the $k$'th event of type $x$ given $history(k-1)$.

#assumption("Bounded number of events")[
In the time interval $[0, tauend]$ there are at most $K - 1 < oo$ many changes of treatment and
    covariates in total for a single individual. The $K$'th event is terminal. 
] <assumptionbounded>

#assumption("No simultaneous jumps")[
    The counting processes $N^a$, $N^ell$, $N^y$, $N^d$, and $N^c$ have with probability 1 no jump times in common.
    #footnote[If the resulting martingales $M^x$, are of locally bounded variation, then the processes are orthogonal $[M^x, M^(x')]_t = 0$ for $x != x'$ $P$ -a.s,
        where $[dot, dot]$ is the quadratic covariation process.]
] <assumptionnosimultaneous>

= Causal framework

Our overall goal is to estimate the interventional cumulative incidence function at time $tau$,
$
    Psi_tau^g (P) = mean(P) [tilde(N)^y (tau)],
$
where $tilde(N)^y (t)$ is the potential outcome (a counting process with at most one jump) representing
the counterfactual outcome $N^y (t) = sum_(k=1)^K bb(1) {event(k) <= t, status(k) =y}$ had the treatment
regime $g$, possibly contrary to fact, been followed. For simplicity, we assume that the treatment
regime specifies that $A(t) = 1$ for all $t >= 0$.
This means that treatment is administered
at each visitation time.
In terms of this data, this means that we must have $A(0) = 1$ and $treat(k) = 1$ whenever $status(k) = a$ and $event(k) < t$.
We now define the càdlàg weight process $(W (t))_(t>=0)$ given by
$
        W (t) = product_(k=1)^(N_t) ((bb(1) {treat(k) = 1}) / (densitytrt(event(k), k)))^(bb(1) {status(k) = a}) (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0))),
$ <eq:weightprocess>
where $N_t = sum_k bb(1) {event(k) <= t}$ is the number of events up to time $t$,
and we consider the observed data target parameter $Psi_tau^"obs" : cal(M) -> RR_+$#footnote[Note that by fifth equality of Appendix S1.2 of @rytgaardContinuoustimeTargetedMinimum2022,
    this is the same as the target parameter in @rytgaardContinuoustimeTargetedMinimum2022 with no competing event.]
 given by
$
        Psi_tau^"obs" (P) = mean(P) [N^y (tau) W (tau)].
$ <eq:identification>
We provide both martingale and non-martingale conditions for the identification ($Psi_tau^g (P) = Psi_tau^"obs" (P)$) of the mean potential outcome in @thm:identifiabilitymartingale and @thm:identifiability,
respectively. One can also define a (stochastic)
intervention with respect to a local independence graph (@roeysland2024) but we do not further pursue this here. //#footnote[The reason we write stochastic is that the treatment consists of two components; the total compensator for the treatment and mark probabilities. Since these two components are inseparable, the intervention of interest is not a static intervention. ]
While our theory provides a potential outcome framework, it is unclear at this point
how graphical models can be used to reason about the conditions. #footnote[see @richardson2013single for the discrete time variant, i.e., single world intervention graphs.]
//We recognize at this point that visitation times may not actually be that irregular,
//but regularly scheduled as they are in a randomized control trial. This will likely _not_ change our results for identification, estimation,
//and debiasing.
//For instance, even if $cumhazard(k, a, t)$ were fully known and deterministic,
//the efficient influence function
//given in @thm:eif and the iterative conditional expectation formula (@eq:ice2 and @eq:ipcw) are not likely to change
//based on the form given in these theorems.

//#assumption("Conditional distributions of jumps")[
//    We assume that the conditional distributions $P(event(k) in dot | history(k-1)) lt.double m$ $P$-a.s., where $m$ is the Lebesgue measure on $RR_+$.
//        ] <assumptionabscont>

//We now take an interventionalist stance to causal inference such as the one given in @ryalenPotentialOutcomes.

== Identification of the causal effect (martingale approach)
Let $N^a_t (dot) = N^alpha ((0, t] times {a} times dot times cal(L))$ be the random measure on $(RR_+ times {0, 1})$ for the treatment process 
and let $Lambda_t^a (dot)$ be the corresponding $P$-$cal(F)_t$ compensator.
We consider a martingale approach for the identification of causal effects similar to the approach taken in @ryalenPotentialOutcomes.
#footnote[The overall difference between @ryalenPotentialOutcomes and our exchangeability condition is that the $P$-$cal(F)_t$ compensator $Lambda^a_t ({1})$ is not required to be the $P$-$(cal(F)_t or sigma(tilde(N)^y))$ compensator for $N^a$.]

To do this this, we define the stopping time $T^a$ as the time of the first visitation event where the treatment plan is not followed, i.e.,
$
    T^a = inf_(t >= 0) {A(t) = 0} = cases(inf_(k > 1) {event(k) | status(k) = a, treat(k) != 1} "if" A(0) = 1, 0 "otherwise")
$

Overall $T^a$ acts as a coarsening variable, limiting
the ability to observe the full potential outcome process. An illustration of the consistency condition in @thm:identifiabilitymartingale is provided in @fig:potentialoutcome.
Informally, the consistency condition states that the potential outcome process $tilde(N)^y (t)$
coincides $N^y (t)$ if the treatment plan is _followed_ at time $t$.

To fully phrase the causal inference problem as a missing data problem,
we also need an exchangeability condition.
The intuition behind the exchangeability condition in @thm:identifiabilitymartingale
is that the outcome process $tilde(N)^y$ should be
independent of both the timing of treatment visits and treatment assignment,
conditional on observed history.

We also briefly discuss the positivity condition,
which ensures that $(W(t))_(t >= 0)$ is a uniformly integrable martingale
with $mean(P) [W(t)] = 1$ for all $t in [0, tauend]$ by @eq:sde. This guarantees
that the observed data parameter $Psi_tau^"obs" (P)$ is well-defined.

Note that instead of conditioning on the entire potential outcome process in the exchangeability condition,
we could have simply conditioned on a single potential outcome variable $tilde(T)_y := inf {t > 0 | tilde(N)^y (t) = 1} in [0, oo]$#footnote[A competing event occuring corresponds to $tilde(T)_y = oo$]
and added that information at baseline #footnote[Note that $bb(1) {tilde(T)_y <= t} = tilde(N)^y (t)$ for all $t > 0$ because $(tilde(N)^y (t))_(t>=0)$ jumps at most once.].
//#footnote[Note that if $N^y (t)$ and $N^y (t)$ are counting processes for an event of interest and a competing event, respectively.
//  L
//then $tilde(T)_y$ is the time of the first event of interest and $T^y$ is the time of the first competing event.
//$bb(1) {T <= t, D = y} = bb(1) {T^y <= t}$.].

We can also state the time-varying exchangeability condition of @thm:identifiabilitymartingale explicitly in terms of the observed data:
Let $cal(H)_(event(k))$ be the corresponding stopping time $sigma$-algebra for the $k$'th event
with respect to the filtration ${cal(H)_t}$ given in @thm:identifiabilitymartingale.
In light of the canonical compensator (@thm:jointdensity (ii)), we see immediately that the exchangeability condition is fulfilled if
$ treat(k) perp tilde(T)_y | event(k), status(k) = a, history(k-1)$
and the cause-specific cumulative hazards for $event(k) | history(k-1), tilde(T)_y$
for treatment visits only depend on $history(k-1)$ and not on $tilde(T)_y$.

// #footnote[It may be shown in
//     contrast that a sufficient condition for the exchangeability condition in @ryalenPotentialOutcomes
//     is that the cumulative cause-specific hazard of $event(k) | cal(H)_(event(k-1)$
//     for treatment visits that assign no treatment do not depend on $tilde(T)_y$,
//     which is actually slightly weaker. If the treatment visitation times are actually not random (i.e., regular),
//     the two stated conditions are the same. //Look into the more general setting.
// ]
//@ryalenPotentialOutcomes requires that the cp $bb(1) {T^a <= t}$

//At this point, it is unclear to me if the conditions, unlike coarsening at random (CAR),
//impose restrictions on the observed data process in terms of the observed outcome. //, i.e., is "locally arbitrary" in the sense described by @onrobinsformula.

#theorem("Martingale identification of mean potential outcome")[
Define
$
    zeta (t, m, a, l) := sum_k bb(1) {event(k-1) < t <= event(k)} ((bb(1) {a = 1}) / (densitytrt(event(k), k)))^(bb(1) {m=a}),
$ <eq:reweightmeasure>

If _all_ of the following conditions hold:
- *Consistency*: $tilde(N)^y (t) bb(1) {T^a > t} = N^y (t) bb(1) {T^a > t} quad P-"a.s."$
- *Exchangeability*:
  Define $cal(H)_t := cal(F)_t or sigma(tilde(N)^y)$.
  The $P$-$cal(F)_t$  compensator for $N^a$ $Lambda^a_t (dot)$ is also the $P$-$cal(H)_t$ compensator
      and
  $
       &tilde(N)^y (t) 
       perp treat(0) | covariate(0), forall t in (0, tauend].
  $
- *Positivity*: $mean(P) [integral bb(1) {t <= tauend} |zeta(t, m, a, l) - 1| W (t-) N (d (t, m, a, l))] < oo$ and $ mean(P) [W(0)] = 1.$
    //$mean(P) [lim_(t -> oo) W(t)] = mean(P) [W(0)] = 1$ and $mean(P) [W (t)^2] < oo$ for all $t > 0$. #footnote[Most likely, it is sufficient for these properties to hold until $tauend$ and not $oo$, because we don't care about identification after that point. ]
  //$densitytrt(event(k), k) > eta$ and $pi_0 (covariate(0)) > eta$ for all $k in {1, dots, K-1}$ and $t > 0$ for some $eta > 0$ $P$-a.s. #footnote[Probably not the most general condition, but it is sufficient for the proof of the theorem.]    //$W (t) = product_(k=1)^(N_t) ((bb(1) {treat(k) = 1}) / (densitytrt(event(k), k)))^(bb(1) {status(k) = a}) (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0))) < eta$ for all $t>0$ (for simplicity)#footnote[Implying that $mean(P) [W (t)] = 1$ for all $t$].  //fulfills $mean(P) [W (t)] = 1$ for all $t in {0, oo}$ (by monotonicity of $L(t)$ all values in between have mean 1).

Then,
$
    Psi_(t)^g (P) = Psi_t^"obs" (P)
$ for all $t in (0, tauend]$.
] <thm:identifiabilitymartingale>

#proof[
    //By @thm:jointdensity (ii), we have that the $P$-$cal(F)_t$ compensator of $N_t (dot)$ is given by 
    //$
    //    Lambda (d (t, x)) = sum_k bb(1) {event(k-1) < t <= event(k)} cumhazard(k,a,dif t) (delta_(1) (dif a) densitytrt(t, k) + delta_(0) (dif a) (1 - densitytrt(t, k))) delta 
    //$
    We shall use that the likelihood ratio solves a specific stochastic differential equation (we use what is essentially Equation (2.7.8) of @andersenStatisticalModelsBased1993),
    but present the argument using Theorem 10.2.2 of @last1995marked as the explicit conditions are not stated in @andersenStatisticalModelsBased1993.
    First, let
    $
        psi_(k, x) (t, history(k-1),dif (m, a, l)) &=   bb(1) {x = a}(delta_(1) (dif a) densitytrt(t, k) + delta_(0) (dif a) (1 - densitytrt(t, k))) delta_(covariate(k-1)) (dif l) \
            &+ bb(1) {x = ell} densitycov(d l, t, k) delta_(treat(k-1)) (dif a) \
            &+ bb(1) {x in {y, d}} delta_(treat(k-1)) (dif a) delta_(covariate(k-1)) (dif l).
$ <eq:mark>
    We shall use that the $P$-$cal(F)_t$ compensator of $N^alpha$ is given by
    $
        Lambda^alpha (d (t, m, a, l)) &= sum_k bb(1) {event(k-1) < t <= event(k)} sum_(x=a,ell,y,d) delta_x (dif m) psi_(k,x) (t, d (a, l)) cumhazard(k,x,dif t) , \
    $ <eq:compensator>
    see e.g., @thm:jointdensity (ii).
    Second, let $Phi (d (t, x)) = bb(1) {t <= tauend} N^alpha (d (t, x))$ and $nu (d (t, x)) = bb(1) {t <= tauend} Lambda^alpha (d (t, x))$ be the restricted
    random measure and its compensator. We define $P$-$cal(F)_t$ predictable, $mu (d (t, x)) := zeta (t, x) nu (d (t, x))$.
    Here, we use the shorthand notation $x=(m,a,l)$.
    The likelihood ratio process $L (t)$ given in (10.1.14) of @last1995marked is defined by
    $
        L(t) &= bb(1) {t < T_oo and T_oo (nu)) L_0 product_(n : event(n) <= t) zeta(event(n), status(n), treat(n), covariate(n)) \
             &quad product_(s <= t \ N_(s-) = N_(s)) (1-macron(nu) {s}) / (1-macron(mu) {s}) exp(integral bb(1){s <= t} (1-zeta(s,x)) nu^c (d (s, x))) \
            &+ bb(1) {t >= T_oo and T_oo (nu)} liminf_(s -> T_oo and T_oo (nu)) L(s).
    $ <eq:lrt>
    Here $T_oo := lim_n T_n$, $T_oo (nu) := inf {t >= 0 | nu ((0, t] times {y, d, a, ell} times {0, 1} times cal(L)) = oo}$,
    $macron(mu)(dot) := mu(dot times {y, d, a, ell} times {0, 1} times cal(L))$,
    $macron(nu)(dot) := nu(dot times {y, d, a, ell} times {0, 1} times cal(L))$,
    $nu^c (dif (s, x)) := bb(1) {macron(nu) {s} = 0} nu (d (s, x))$, and $L_0 := W (0) = (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0)))$.
    
    First, we will show that $L(t) = W (t)$, where $W (t)$ is the weight process defined in @eq:weightprocess.

    Note that by @assumptionbounded, $T_oo = oo quad P $-a.s. and 
    thus $T_oo (nu) = T_oo = oo$ in view Theorem 4.1.7 (ii) since $macron(nu) {t} < oo$ for all $t > 0$.
    
    Second, note that $macron(nu) = macron(mu)$. This follows since
    $
        macron(nu) (A) &= integral_(A times {y, d, a, ell} times {0, 1} times cal(L)) zeta(t, m, a, l) mu (d (t, m, a, l)) \
            &=integral_(A times {y, d, ell} times {0, 1} times cal(L)) zeta(t, m, a, l) mu (d (t, m, a, l))  + integral_(A times {a} times {0, 1} times cal(L)) zeta(t, m, a, l) mu (d (t, m, a, l))\
            &=integral_(A times {y, d, ell} times {0, 1} times cal(L)) 1 mu (d (t, m, a, l))  + integral_(A times {a} times {0, 1} times cal(L)) zeta(t, m, a, l) mu (d (t, m, a, l))\
            &=mu (A times {y, d, ell} times {0, 1} times cal(L))  + sum_k bb(1) {event(k-1) < t <= event(k)} Lambda^a (d t | history(k-1)) \
            &=mu(A times {y, d, a, ell} times {0, 1} times cal(L)) = macron(mu) (A), \
    $
    for Borel measurable sets $A subset.eq RR_+$,
    where the last step follows from the form of the compensator (@eq:compensator).
    Thus
    $
        product_(s <= t \ N_(s-) = N_(s)) (1-macron(nu) {s}) / (1-macron(mu) {s}) exp(integral bb(1){s <= t} (1-zeta(s,x)) nu^c (d (s, x))) = 1,
    $
    and hence
    $
        L(t) &= L_0 product_(n : event(n) <= t) zeta(event(n), status(n), treat(n), covariate(n)) \
            &=^"def."W (t).
    $
    Let $V(s,x) = zeta(s,x) - 1 + (macron(nu) {s}-macron(mu) {s})/(1-macron(mu) {s}) = zeta(s,x)-1$.
    $L (t)$ will fulfill that
    $
        L (t) = L_0 + integral bb(1) {s <= t} V(s,x) L(s-) [Phi (d(s,x)) - nu (d(s,x))] \
    $
    if
    $
        mean(P) [L_0] = 1, \
        macron(mu) {t} <= 1, \
        macron(mu) {t} = 1 " if " macron(nu) {t} = 1, \
        macron(mu) [T_oo and T_oo (mu)] = 0 " and " macron(nu) [T_oo and T_oo (nu)] = 0.
    $ <eq:conditionstheorem1022>
    by Theorem 10.2.2 of @last1995marked.
    
    The first condition holds by positivity. The second condition holds by the specific choice
    of compensator since $sum_x cumhazard(k, x, {t}) <= 1$ for all $k = 1, dots, K$ and $t in (0, tauend]$ (Theorem A5.9 of @last1995marked).
    The third holds since $macron(mu) = macron(nu)$ and the fourth holds since $T_oo = T_oo (nu) = T_oo (mu) = oo$.
    
    Thus,
    $
        W(t) = (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0))) + integral_0^t W(s -) V(s, x) (Phi (d(s,x)) - nu (d(s,x)).
    $ <eq:sde>
    
    Then we shall show that
    $
        M^*_t := integral tilde(N)^y (t) bb(1) {s <= t} V(s,x) L(s-) [N (d(s,x)) - Lambda (d(s,x))]
    $ <eq:martingalecond>
    is a zero mean uniformly integrable martingale.
    This follows if
    $
        mean(P) [integral tilde(N)^y (t) |V(s,x)| L(s-) Phi (d(s,x))] < oo.
    $
    and if $(omega, s, x) mapsto tilde(N)^y (t) |V(s,x)| L(s-)$ is $P$-$cal(H)_s$ predictable by Exercise 4.1.22 of @last1995marked.
    Since
    $
        mean(P) [integral tilde(N)^y (t) |V(s,x)| L(s-) Phi (d(s,x))] <= mean(P) [integral bb(1) {s <= tauend} |V(s,x)| L(s-) N (d(s,x))] < oo
    $
    and
    $(omega, s) mapsto tilde(N)^y (t)$ is predictable with respect to $cal(H)_s$,
    $(omega,s) mapsto L(s-)$ is $P$-$cal(H)_s$ predictable (càglàd and adapted; Theorem 2.1.10 of @last1995marked),
    $(omega,s, x) mapsto V(s,x)$ is $P$-$cal(H)_s$ predictable (Theorem 2.2.22 of @last1995marked),
    so that $(omega, s) mapsto tilde(N)^y (t) |V(s,x)| L(s-)$ is $P$-$cal(H)_s$ predictable,
    and the desired martingale result for @eq:martingalecond follows.
    This in turn implies by @eq:sde:
    $
        mean(P) [ tilde(N)_t^y W(t)] &= mean(P) [ tilde(N)_t^y W(0)] + mean(P) [M^*_t] \
            &= mean(P) [ tilde(N)_t^y W(0)] \
            &= mean(P) [ mean(P) [tilde(N)_t^y | history(0)] W(0) ] \
            &= mean(P) [ mean(P) [tilde(N)_t^y | covariate(0)] W(0) ] \
            &= mean(P) [ mean(P) [tilde(N)_t^y | covariate(0)] mean(P) [W(0) | covariate(0)] ] \
            &= mean(P) [ mean(P) [tilde(N)_t^y | covariate(0)] 1] \
            &= mean(P) [ tilde(N)_t^y],
    $
    where we use the baseline exchangeability condition and the law of iterated expectation.
]
// Note that we can specify conditions directly in terms of the events. 

#figure(cetz.canvas(length: 1cm, {
    import cetz.draw: *

  // Set-up a thin axis style
  set-style(axes: (stroke: .5pt, tick: (stroke: .5pt)),
      legend: (stroke: none, item: (spacing: .3), scale: 80%))
    line( (0,0), (0,6), mark: (end: ">"), name: "line")
    line( (0,0), (6,0), mark: (end: ">"), name: "line")
    content((), $t$, anchor: "north-west")
    line((0, 2.3),(-0.15, 2.3))
    content((), $1$, anchor: "east")
    line((0, 0.3),(-0.15, 0.3))
    content((), $0$, anchor: "east")

    line( (0.1,0.3), (3,0.3), mark: ( end: "o"), stroke: (paint: blue))
    line( (2.7,2.3), (5,2.3), mark: (fill: blue, start: "o"), stroke: (paint: blue))
    line( (3,0.3), (5,0.3), mark: (fill: blue), stroke: (dash: "dashed", paint: blue))
    line( (1.8, 0.15), (1.8, -0.15))
    content((), $T^a$, anchor: "north")
    
    line( (8,0), (8,6), mark: (end: ">"), name: "line")
    content((), $A(t)$, anchor: "east")
    line( (8,0), (14,0), mark: (end: ">"), name: "line")
    content((), $t$, anchor: "north-west")
    line((8, 2.3),(7.85, 2.3))
    content((), $1$, anchor: "east")
    line((8, 0.3),(7.85, 0.3))
    content((), $0$, anchor: "east")

    line( (8.1,2.3), (9.8,2.3), mark: ( end: "o"), stroke: (paint: blue))
    line( (9.7,0.3), (13,0.3), mark: (fill: blue, start: "o"), stroke: (paint: blue))
    line( (9.8, 0.15), (9.8, -0.15))
    content((), $T^a$, anchor: "north")
}), caption: [The figure illustrates the consistency condition for the potential outcome framework for single individual.
    The left panel shows the potential outcome process $tilde(N)^y (t)$ (dashed) and the observed process $N^y (t)$ (solid).
    The right panel shows the treatment process $A(t)$. At time $T^a$, the treatment is stopped and the processes
    may from some random future point diverge from each other.
]) <fig:potentialoutcome>

== Identification of the causal effect (non-martingale approach)
In this subsection, we present a non-martingale approach for the identification of causal effects,
and the conditions are stated for identification at the time horizon of interest.

#theorem[
Assume *Consistency* and *Positivity* as in @thm:identifiabilitymartingale for a single timepoint $tau$ (in the positivity condition replace $tauend$ with $tau$). Additionally, we assume that:
- *Exchangeability*: We have
   $
       &tilde(N)^y (tau) bb(1) {event(j) <= tau < event(j+1)}
       perp treat(k) | history(k-1), event(k), status(k) = a, quad forall j>=k>0, \
       &tilde(N)^y (tau) bb(1) {event(j) <= tau < event(j+1)}
       perp treat(0) | covariate(0), quad forall j>=0.
   $ <eq:exchangeability>

Then the estimand of interest is identifiable, i.e.,
$
    Psi_(tau)^g (P) = Psi_tau^"obs" (P).
$
]<thm:identifiability>
#proof[
    Write $tilde(Y)_t = sum_(k=1)^K bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau)$.
    The theorem is shown if we can prove that $mean(P) [bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau)] = mean(P) [bb(1) {event(k-1) <= tau < event(k)} N_tau^y W(tau)]$
    by linearity of expectation.
    We have that for $k >= 1$,
    $
        bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} N_tau^y W(tau)] &= bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} bb(1) {T^a > tau} N_tau^y W(tau)] \
            &=bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} bb(1) {T^a > tau} tilde(N)^y (tau) W(tau)] \
            &=bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau) W(tau)] \
            &=bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau) W(event(k-1)) ]\
            &=bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau) ((bb(1) {treat(k-1) = 1}) / (densitytrtprev(event(k-1), event(k-1), k)))^(bb(1) {status(k-1) =a}) W(event(k-2)) ]\
            &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau) | history(k-2), status(k-1), event(k-1), treat(k-1)] \
                &qquad times ((bb(1) {treat(k-1) = 1}) / (densitytrtprev(event(k-1), event(k-1), k)))^(bb(1) {status(k-1) =a}) W(event(k-2)) ]\
                        &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau< event(k)} tilde(N)^y (tau) | history(k-2), status(k-1), event(k-1)] \
                &qquad times ((bb(1) {treat(k-1) = 1}) / (densitytrtprev(event(k-1), event(k-1), k)))^(bb(1) {status(k-1) =a}) W(event(k-2)) ]\
            &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau) | history(k-2), status(k-1), event(k-1)] \
                &qquad times mean(P) [((bb(1) {treat(k-1) = 1}) / (densitytrtprev(treat(k-1), event(k-1), k)))^(bb(1) {status(k-1) =a}) | history(k-2), status(k-1), event(k-1)] W(event(k-2)) ]\
            &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau) | history(k-2), status(k-1), event(k-1)] W(event(k-2)) ]\
            &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau) | history(k-3), status(k-2), event(k-2), treat(k-2)] W(event(k-2)) ]\
    $
    Iteratively applying the same argument, we get that
    $bb(E)_P [  bb(1) {event(k-1) <= tau < event(k)} tilde(N)^y (tau) ] = bb(E)_P [  bb(1) {event(k-1) <= tau < event(k)} N_tau^y W(tau)]$ as needed.
]
By the intersection property of conditional independence, we see that a sufficient condition for the first exchangeability condition in @eq:exchangeability
is that
$
    tilde(N)^y (tau)
    perp treat(k) | event(j) <= tau < event(j+1), history(k-1), event(k), status(k) = a, quad forall j>=k>0, \
    bb(1) {event(j) <= tau < event(j+1)}
    perp treat(k) | history(k-1), event(k), status(k) = a, quad forall j>=k>0. \
$

The second condition may in particular be too strict in practice as the future event times
may be affected by prior treatment.
Alternatively, it is possible to posit the existence of a potential outcome for each event separately and
get the same conclusion. The overall exchangeability condition may be stated differently, but the consistency condition is very similar. 
Specifically, let $tilde(Y)_(tau, k)$ be the potential outcome at event $k$
corresponding to $bb(1) {event(k) <= tau, status(k) =y}$.
Then the exchangeability condition is that $tilde(Y)_(tau, k) perp treat(j) | history(j-1), event(j), status(j) = a)$ for $0 <= j < k$ and $k = 1, dots, K$.
However,
it has been noted (@RobinsLongitudinal2001) in discrete time that the existence of multiple potential outcomes
can be restrictive and that the resulting exchangeability condition may be too strong. 

== Iterated representation of the target parameter

In this section, we present a simple iterated representation of the observed data target parameter $Psi_tau^"obs" (P)$.
We give an iterated conditional expectations formula for the target parameter in the case with no censoring.
To do so, define
$
    S_k (t | history(k-1)) = product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) Lambda_k^x (dif s | history(k-1))), k = 1, dots, K
$
where $product_(s in (0, t])$ is the product integral over the interval $(0, t]$ (@gill1990survey).
We discuss more thoroughly the implications of this representation in the next section,
where we deal with right-censoring.

//Note that the iterative conditional expectations formula in terms of the event-specific cause-specific hazards
//and the density for the time-varying covariates (@thm:hazardrepresentation) actually shows
//that our target parameter is the same as the one given in @rytgaardContinuoustimeTargetedMinimum2022
//with no competing event (*TODO*: show this more explicitly) under the stated identifiability conditions.

//First, and foremost though, we will remark
//that this can be used to write down the target parameter directly in terms of the event-specific cause-specific hazards
//and the density for the covariate process. 

// should just be identification not of conditional densities
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
        Psi_tau^"obs" (P) = mean(P) [Qbar(0) (1, covariate(0))].
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
    Let $W_(k, j) = (W (event(j))) / (W(event(k)))$ for $k < j$ (defining $0/0 = 0$).
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
    A similar calculation shows that $Psi_tau^"obs" (P) = mean(P) [Qbar(0) (1, covariate(0))]$
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

= Censoring
In this section, we introduce a right-censoring time $C>0$
at which we stop observing the multivariate jump process
$alpha(t)$. We present conditions such that our ICE-IPCW estimator
will be consistent for the target parameter.
//We will tacitly assume that $C$ exists and is finite when
//death occurs before the censoring time.
Specifically $N^c (t) = bb(1) {C <= t}$ the counting process for the censoring process and
let $T^e$ further denote the (uncensored) terminal event time given by $T^e = inf_(t>0) {N^y (t) + N^d (t) = 1}$.
Throughout the rest of the paper,
we will assume that the process $N^c$ does not jump at the same time as the processes $N^a, N^ell, N^y, N^d$.

Let $beta(t) = (alpha(t), N^c (t))$ be the fully observable multivariate jump process in $[0, tauend]$.
Then, we observe the trajectories of the process given by $t mapsto beta (t and C and T^e) := tilde(beta) (t)$,
and the observed filtration is given by $cal(F)_t^tilde(beta) = sigma(beta(s and C and T^e) | s <= t) = cal(F)_(t and C) or cal(G)_(t and T^e)$ #footnote[The fact that the stopped filtration and the filtration generated by the stopped process are the same is not obvious but follows by Theorem 2.2.14 of @last1995marked. This can fail if $cal(F)_0$ includes all null-sets.],
where $cal(G)_t = sigma(N^c (s) | s <= t)$ denotes the filtration generated by the censoring process
(for a stopping time $T>0$, we use $cal(F)_(t and T)$ to denote stopping time $sigma$-algebra given by the stopping time $t and T$.).
Let $(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k))$ be the observed data given by 
$
    eventcensored(k) &= C and event(k) \
    statuscensored(k) &= cases(status(k) "if" C > event(k), "c" "otherwise") \
    treatcensored(k) &= cases(treat(k)"if" C > event(k), treat(k-1) "otherwise") \
    covariatecensored(k) &= cases(covariate(k) "if" C > event(k), covariate(k-1) "otherwise")
$
for $k = 1, dots, K$. From this, it follows that
$
    history(k) = historycensored(k) quad "if" statuscensored(k) != c.
$
//and from this point onwards, we shall only work with $history(k)$ as the only case where they differ is when $statuscensored(k) = c$
//and this case we do not care about. 

Also define the full data filtration for $beta$ given by $cal(F)^beta_t = sigma(beta(s) | s <= t) = sigma(alpha(s), N^c (s)) | s <= t)$.
Let $cumhazardcensored(k, c, dif t)$ be the cause-specific cumulative hazard (measure) of the $k$'th event at time $t$ given the observed history $historycensored(k-1)$
and define the corresponding censoring survival function $tilde(S)^c (t | historycensored(k-1)) = prodint(s, event(k-1), t) (1 - cumhazardcensored(k, c, dif s))$.
This determines the observational probability that you will be censored after time $t$ given the observed history
up to $historycensored(k-1)$.

// Denote by
//     $
//         N^(r,a) (d t, d a) &= sum_(k=1)^K delta_(status(k)) (a) delta_((event(k), treat(k))) (d t, d a) \
//         N^(r,ell) (d t, d ell) &= sum_(k=1)^K delta_(status(k)) (ell) delta_((event(k), covariate(k))) (d t, d ell) \
//         N^(r,y) (d t) &= sum_(k=1)^K delta_(status(k)) (y) delta_(event(k)) (d t) \
//         N^(r,d) (d t) &= sum_(k=1)^K delta_(status(k)) (d) delta_(event(k)) (d t) \
//         N^(r,c) (d t) &= sum_(k=1)^K delta_(status(k)) (c) delta_(event(k)) (d t)
//     $
// the corresponding random measures of the fully observed $Z(t)$ and $N^c (t)$.

We provide the conditions in terms of independent censoring.
Our conditions are similar to those that may be found the literature based on independent censoring (@andersenStatisticalModelsBased1993; Definition III.2.1)
or local independence conditions (@roeysland2024; Definition 4).
Heuristically, one may think of independent censoring in this setting as
$
    &P(event(k) in [t, t + dif t), status(k) = x, treat(k) = m, covariate(k) = l | history(k-1), event(k) >= t) \
        &= P(eventcensored(k) in [t, t + dif t), statuscensored(k) = x, treatcensored(k) = m, covariatecensored(k) = l | history(k-1), eventcensored(k) >= t), qquad x!= c.
$
// FLemming and Harrington; generalization of Theorem 1.3.2.
// to proven when I feel like it.
for uncensored histories, i.e., when $statuscensored(k-1) != c$.
We are now ready to state the main theorem
which proves that the ICE-IPCW estimator is valid.
Later, we provide an implementation and algorithm for the ICE-IPCW estimator.

#theorem[
    //Let $N^beta$ be the associated random measure for the full data process $beta$.
    Assume that the compensator $Lambda^alpha$ of $N^alpha$ with respect to the filtration $cal(F)^beta_t$ is
    also the compensator with respect to the filtration $cal(F)_t$.
    Then for uncensored histories, we have 
    $
        &bb(1) {statuscensored(n-1) != c} P ((macron(T)_(n), macron(Delta)_(n), A(macron(T)_(n)), L(macron(T)_(n))) in d (t, m, a,l)| historycensored(n-1)) \
            &= bb(1) {macron(T)_(n-1) < t,statuscensored(n-1) != c} (tilde(S) (t- | history(n-1)) sum_(x=a,ell,d,y) delta_x (dif m) psi_(n,x) (t, d(a, l)) cumhazard(n, x, dif t) \
                &qquad + delta_((c, treat(n-1), covariate(n-1))) (dif (m, a, l)) tilde(Lambda)_(n)^c (dif t, history(n-1))),
    $ <eq:densitycens>
    where $psi_(n,x)$ was defined in @eq:mark
    and $bb(1) {statuscensored(n-1) != c} tilde(S) (t | history(k-1)) = bb(1) {statuscensored(n-1) != c} product_(s in (event(k-1),t]) (1 - sum_(x=a,ell,y,d) Lambda_k^x (dif s | history(k-1)) - tilde(Lambda)_k^c (dif s | history(k-1)))$.
    
    Further suppose that $bb(1) {statuscensored(n-1) != c} product_(s in (event(k-1),t]) (1 - sum_(x=a,ell,y,d) Lambda_k^x (dif s | history(k-1)) - tilde(Lambda)_k^c (dif s | history(k-1)))
    = bb(1) {statuscensored(n-1) != c} product_(s in (event(k-1),t]) (1 - sum_(x=a,ell,y,d) Lambda_k^x (dif s | history(k-1))) product_(s in (event(k-1),t]) (1- tilde(Lambda)_k^c (dif s | history(k-1))) quad P"-a.s."$
    and that $tilde(S)^c (t | historycensored(n-1)) > eta$ for all $t in (0, tau]$ and $n in {1, dots, K}$
    $P$-a.s. for some $eta > 0$.

    Then, the ICE-IPCW estimator is consistent for the target parameter, i.e.,
    #math.equation(block: true, numbering: "(1)")[$
        bb(1) {statuscensored(k-1) != c} Qbar(k-1) &= bb(1) {statuscensored(k-1) != c} mean(P) [(bb(1) {eventcensored(k) < tau, statuscensored(k) = ell})/( tilde(S)^c (eventcensored(k-1) - | historycensored(k-1)) ) Qbar(k)(treatcensored(k-1), covariatecensored(k), eventcensored(k), statuscensored(k), historycensored(k-1)) \
            &#h(1.5cm) + (bb(1) {eventcensored(k) < tau, statuscensored(k) = a}) /(tilde(S)^c (eventcensored(k-1) - | historycensored(k-1)))  Qbar(k) (1, covariatecensored(k-1), eventcensored(k), statuscensored(k), historycensored(k-1)) \
            &#h(1.5cm) + (bb(1) {eventcensored(k) <= tau, statuscensored(k) = y}) /(tilde(S)^c (eventcensored(k-1) - | historycensored(k-1))) mid(|) historycensored(k-1)]
    $] <eq:ipcw>
    for $k = K, dots, 1$ and
    $
        Psi_tau^"obs" (P) = mean(P) [  Qbar(0) (1, covariate(0))].
    $<eq:ice2>
] <thm:ice>
#proof[
    // positivity?
    Under the local independence condition, the compensator of the random measure $N^alpha (dif (t, m, a, l))$ with respect to the filtration $cal(F)^beta_t$,
    can be given by (@thm:jointdensity (ii))
    $
        Lambda^alpha (dif (t,m, a, l)) &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} sum_(x=a,ell,d,y) delta_x (dif m) psi_(k,x) (t, d(a, l), history(k-1)) cumhazard(k, m, dif t).
        //phi_(k,x) (t, d(a, l)) &= bb(1) {m!=c} hazard(x, t, k-1) densitytrtmeasure(t, dif a, k-1) densitycov(t, dif l, k-1) d t \
        //    &qquad + bb(1) {m=c} hazard(x, t, k-1) densitytrtmeasure(t, dif a, k-1) densitycov(t, dif l, k-1) d t \
        //Lambda^beta (dif t) &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} hazard(x, t, k-1) d t
    $
    In view of this, the stopped process $N^(tilde(beta))$ has by the optional sampling theorem (the corollary after I Theorem 18 of @protter2005stochastic since $C and T^e < oo$)
    a compensator given by
    $
        Lambda^tilde(beta) (dif (t, m, a, l)) &= sum_(k=1)^K bb(1) {event(k-1) and C < t <= event(k) and C} sum_(x=a,ell,d,y) delta_x (dif m) psi_(k,x) (t, d(a, l), history(k-1)) cumhazard(k, m, dif t) \
            &qquad + delta_((c, treat(k-1), covariate(k-1))) (dif (m, a, l)) tilde(Lambda)_k^c (dif t | history(k-1)) \
        //phi_(k,x) (t, d(a, l)) &= bb(1) {m!=c} hazard(x, t, k-1) densitytrtmeasure(t, dif a, k-1) densitycov(t, dif l, k-1) d t \
        //    &qquad + bb(1) {m=c} hazard(x, t, k-1) densitytrtmeasure(t, dif a, k-1) densitycov(t, dif l, k-1) d t \
        //Lambda^beta (dif t) &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} hazard(x, t, k-1) d t
    $<eq:canonical>
    with respect to the filtration $cal(F)^tilde(beta)_t$ (to obtain the censoring term, we find a compensator for $N^(tilde(beta))$ with respect to $cal(F)^(tilde(beta))$ again by @thm:jointdensity (ii) and obtain the component corresponding to censoring).

    Let $N_bold(X)$ denotes the space of all point process trajectories
    with mark space $bold(X)$.
    Note that as $historycensored(n)$ is generated by finitely many random variables,
    there is a measurable function $h_n$ with the property that $h_n ((treat(0), covariate(0)), N^(tilde(beta)) (dot and event(n))) = history(n)$.
    We can define
    then stochastic kernel from ${0,1} times cal(L) times N_bold(X)$ to $RR_+ times bold(X)$ with $bold(X) = {a,y,ell,d, c} times {0,1} times cal(L)$
    by
    $
        rho ((l_0,a_0), phi, d (t, m, a, l)) &= sum_(k=1)^K bb(1) {zeta_(n-1) (phi) < t <= zeta_(n) (phi)} sum_(x=a,ell,d,y) delta_x (dif m) psi_(k,x) (t, d(a, l), h_n (phi)) ) Lambda_k^x (d t,  h_n (phi)) \
            &+ delta_(c, eta^a_(n-1) (phi), eta^ell_(n-1) (phi)) (dif (m, a, l)) tilde(Lambda)_k^c (d t | h_n (phi)) \
    $
    where $zeta_n$ denotes the projection operator to the $n$'th event, // and $phi_(T_n)$ denotes the future process after $n$ events,  i.e., the restriction the set $(event(n), oo) times cal(X)$.
    where $eta_j^a$ is the projection operator to the $j$'th events treatment mark and $eta_j^ell$ is the projection operator to the $j$'th events covariate mark.
    It is the canonical compensator because $rho ((covariate(0),treat(0)), N^(tilde(beta)), d (t, m, a, l))$
    is a compensator of the process $N^(tilde(beta))$ with respect to the filtration $cal(F)^(tilde(beta))_t$ (@last1995marked; p. 130).

    The conditional distribution of the event and marks then follows from this via Theorem 4.3.8 of @last1995marked. The theorem specifically states that
    $
        &P ( (macron(T)_k, macron(Delta)_k, A(macron(T)_k), L(macron(T)_k)) in d (t, m, a,l) | historycensored(k-1)) \
            &= bb(1) {macron(T)_(k-1) < t} product_(s in (macron(T)_(k-1), t)) (1-rho ((l_0,a_0), macron(N)_(macron(T)_(k-1)), d s, {a,y,l,d,y} times {0,1} times cal(L)))) rho ((l_0,a_0), macron(N)_(macron(T)_(k-1)), d (t, m, a, l)).
    $
    where $N^(tilde(beta))_(macron(T)_n)$ is a shorthand for $N^(tilde(beta)) (dot and eventcensored(n))$.
    We find
    $
        bb(1) {macron(T)_(k-1) < t, statuscensored(k-1) != c} alpha ((l_0,a_0), N^(tilde(beta))_(macron(T)_(k-1)), d (t, m, a, l)) &= bb(1) {statuscensored(k-1) != c} (sum_(x=a,ell,d,y) delta_x (dif m) psi_(k,x) (t, d(a, l), history(k-1)) Lambda_k^x (d t,  history(k-1)) \
            &+ delta_(c, covariate(k-1), treat(k-1)) (dif (m, a, l)) tilde(Lambda)_k^c (d t | history(k-1))) \
    $
    and
    $
        bb(1) {macron(T)_(k-1) < t, statuscensored(k-1) != c} alpha ((l_0,a_0), N^(tilde(beta))_(macron(T)_n), d s, {a,y,l,d,y} times {0,1} times cal(L)) &= bb(1) {statuscensored(k-1) != c} (sum_(x=a,ell,d,y) Lambda_k^x (d t,  history(k-1)) +  tilde(Lambda)_k^c (d t | history(k-1))).
    $
    From this, we get @eq:densitycens.
    Applying this to the right hand side of @eq:ipcw
    shows that it is equal to @eq:iterative.    
    
    //Conversely suppose that $tilde(S) (t- | cal(F)^tilde(beta)_(macron(T)_k)) = 0$.
    //This means that $sum_(x=a,l,y,d) Delta cumhazard(k+1, x, t) + Delta tilde(Lambda^c)_(k+1) (t | tilde(cal(F))_(tilde(T)_((k)))) = 0$. 
    //for some $u in (macron(T)_(k), t)$, $Delta tilde(Lambda^c)_(k+1) (u | tilde(cal(F))_(tilde(T)_((k)))) = 1$.
    //but this is exactly the set of $t$'s that we need to show @eq:tildeSfactor.
    // note write bounded variation here
       
]

Note that @eq:densitycens also ensures that all hazards (other than censoring) and mark probabilities are identifiable from censored data
if we can show that the censoring survival factorizes.
We provide two criteria for this.

#theorem[
    Assume that for each $k = 1,dots, K$,
    $
        (event(k),status(k),treat(k),covariate(k)) perp C | history(k-1)
    $
    Then the survival function factorizes
    $
        tilde(S) (t | cal(F)^tilde(beta)_(macron(T)_k)) &= product_(s in (0, t)) (1 - (sum_(x=a,ell,y,d) cumhazard(k, x, dif s) +  tilde(Lambda)_k^c (dif t | historycensored(k-1)))) \
            &=product_(s in (0, t)) (1 - sum_(x=a,ell,y,d) cumhazard(k, x, dif s)) product_(s in (0, t]) (1 - tilde(Lambda)_k^c (dif t | historycensored(k-1))) 
    $
    and the local independence statement given in @eq:densitycens holds.
]

#proof[
    By the stated independence condition, it follows immediately that
    $
        tilde(S) (t | cal(F)^tilde(beta)_(macron(T)_k)) &= P(event(k) > t, C > t| cal(F)^tilde(beta)_(macron(T)_k)) = S(t | cal(F)^tilde(beta)_(macron(T)_k)) S^c (t | cal(F)^tilde(beta)_(macron(T)_k)) \
    $
    All we need to show for the first statement is, 
    $
        S^c (t | cal(F)^tilde(beta)_(macron(T)_k)) = product_(s in (0, t]) (1 - tilde(Lambda)_k^c (dif s | historycensored(k-1)))
    $
    which follows "directly" by calculating $P(eventcensored(k) in dif t, status(k) = c | historycensored(k-1))$
    and from this we get the observed cause-specific hazards.

    The local independence statement follows by letting $tilde(cal(F))^beta = sigma(alpha(s) | s <= t) or cal(Z)_0$, where $cal(Z)_0 = sigma(treat(0), covariate(0), C)$.
    Evidently, $cal(F)_t subset.eq cal(F)^beta_t subset.eq tilde(cal(F))^beta_t$.
    Under the independence assumption, by the use of the canonical compensator,
    the compensator for $N^alpha$ for $cal(F)_t$ is also the compensator for $tilde(cal(F))^beta_t$.
    Let $M^alpha$ denotes the corresponding martingale decomposition. It follows that:
    $
        &mean(P) [M^alpha ((0,t] times {a,ell,y,d,c} times {0,1} times cal(L)) | cal(F)^beta_s] \
            &=mean(P) [mean(P) [M^alpha ((0,t] times {a,ell,y,d,c} times {0,1} times cal(L)) | tilde(cal(F))^beta_s]| cal(F)^beta_s] \
            &=^"(i)"mean(P) [M^alpha ((0,s] times {a,ell,y,d,c} times {0,1} times cal(L)) | cal(F)^beta_s] \
            &=^"(ii)"M^alpha ((0,s] times {a,ell,y,d,c} times {0,1} times cal(L)) \
    $
    which implies the desired statement. In part (i), we that the martingale is a martingale for $tilde(cal(F))^beta_t$.
    In part (ii), we use that the martingale is $cal(F)_t^alpha$-adapted. 
]

*Not cleaned*

Finally, we need to show that the survival function factorizes
    $
        tilde(S) (t- | cal(F)^tilde(beta)_(macron(T)_k)) &= product_(s in (0, t)) (1 - (sum_(x=a,ell,y,d) cumhazard(k, x, dif s) +  tilde(Lambda)_k^c (dif t | historycensored(k-1)))) \
            &=product_(s in (0, t)) (1 - sum_(x=a,ell,y,d) cumhazard(k, x, dif s)) product_(s in (0, t]) (1 - tilde(Lambda)_k^c (dif t | historycensored(k-1))) 
    $ <eq:tildeSfactor>




for in doing so, we can apply @eq:densitycens and @eq:tildeSfactor show that the right hand side of @eq:ipcw
    is the same as the left hand side of @eq:ipcw. But the factroization holds
    since
    $
        product_(v in (s, t)) (1 - d (zeta+gamma)) = exp(-beta^c) exp( -gamma^c) product_(v in (s, t) gamma(v) != gamma(v-) or zeta(v) != zeta(v-))  (1 - Delta ( zeta+gamma))
    $
    since the processes $zeta$ and $gamma$ do not jump at the same time, the last factor factorizes, i.e.,
    $
        product_(v in (s, t) gamma(v) != gamma(v-) or zeta(v) != zeta(v-))  (1 - Delta (zeta+gamma)) = product_(v in (s, t) \ gamma(v) != gamma(v-)) (1- Delta gamma) product_(v in (s, t) \ zeta(v) != zeta(v-)) (1 - Delta zeta)
    $

Further suppose that $[M^c, M^x]= 0$ for $x in {a, ell, d, y}$. Then,
    $tilde(S) (t | history(n-1))$ is given by
    $
        tilde(S) (t | history(n-1)) &= S (t | history(n-1)) tilde(S)^c (t | history(n-1)) 
    $
For this, we only that the censoring does not jump at the same time as any of the other counting processes.
    To show this, consider the quadratic covariation which by orthogonality implies
    $
        0=[M^c,sum_x M^x] = integral_0^dot Delta tilde(Lambda)_c sum_(x=a,ell,y,d) d Lambda_x
    $
Using this, we have
$
    0 &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} integral_((event(k-1), t]) Delta tilde(Lambda)_c (sum_(x=a,ell,y,d) d Lambda_x) \
      &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} integral_((event(k-1), t]) Delta cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) cumhazard(k, x, dif s))),
$
so that $bb(1) {event(k-1) < t <= event(k)} integral_((event(k-1), t]) Delta (cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) cumhazard(k, x, dif s))) = 0$.
    Taking the expectations on both sides, we have
    $
        tilde(S) (t- | cal(F)^tilde(beta)_(macron(T)_k)) sum_(macron(T)_(k) < s <= t) (Delta tilde(Lambda^c)_(k+1)) (s | tilde(cal(F))_(tilde(T)_((k)))) (sum_(x=a,ell,y,d) Delta cumhazard(k+1, x, s)) = 0 
    $
    It follows that for every $t$ with $tilde(S) (t- | cal(F)^tilde(beta)_(macron(T)_k)) > 0$,
    $
        sum_(macron(T)_(k) < s <= t) (Delta tilde(Lambda^c)_(k+1)) (s | tilde(cal(F))_(tilde(T)_((k)))) (sum_(x=a,ell,y,d) Delta cumhazard(k+1, x, s)) = 0
    $

If we can further argue that $Delta tilde(Lambda)_(k+1)^c + sum_x Delta cumhazard(k+1, x, t)=1 => Delta tilde(Lambda)_(k+1)^c = 1 or sum_x Delta cumhazard(k+1, x, t) = 1$
because these are the only points at which $tilde(S)$ can be zero, but not the two other survival functions. Alternatively, it may be assumed that
$Delta tilde(Lambda)_(k+1)^c + sum_x Delta cumhazard(k+1, x, t) < 1$ to get the desired statement. 
//The other representations of the target parameter in terms of the intensities are useful directly,
//but we may, as in the discrete, estimate the target parameter by Monte Carlo integration (i.e., direct simulation from the estimated intensities/densities).

In the next section, we will now write $event(k), status(k), treat(k), covariate(k)$ instead of $eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k)$
and $history(k)$ instead of $historycensored(k)$. *NOTE*: Change this. 

A simple implementation of the IPCW is provided in @alg:ipcwice.


== Algorithm for IPCW Iterative Conditional Expectations Estimator <alg:ipcwice>

The following algorithm gives a simple implementation of the IPCW ICE estimator.
We assume that $K$ denotes the last non-terminal event in the sample before time $tau$.

- For each event point $k = K, K-1, dots, 1$ (starting with $k = K$):
    1. Obtain $hat(S)^c (t | history(k-1))$ by fitting a cause-specific hazard model for the censoring via the interevent time $S_((k)) = event(k) - event(k-1)$,
       regressing on $history(k-1)$ (among the people who are still at risk after $k-1$ events).
    2. Define the subject-specific weight:
       $
           hat(eta)_k = (bb(1) {event(k) <= tau, Delta_k in {a, ell}, k < K} hat(nu)_(k) (cal(F)^(-A)_(event(k)), bold(1))) / (hat(S)^c (event(k)- | history(k-1)))
       $
       Then calculate the subject-specific pseudo-outcome
       $
           hat(R)_k &= (bb(1) {event(k) <= tau, Delta_k = y}) / (hat(S)^c (event(k) - | history(k-1))) + hat(eta)_k
       $
       Regress $hat(R)_k$ on $history(k-1)$ on the data with $event(k-1) < tau$ and $Delta_k in {a, ell}$ to obtain a prediction function $hat(nu)_(k-1) : cal(H)_(k-1) -> RR_+$.
           
- At baseline, we obtain the estimate $hat(Psi)_n = 1/n sum_(i=1)^n hat(nu)_(0) (L_i (0), 1)$.

The high dimensionality of the second representation given in @thm:parameter
makes it likely that is not useful for computing the target parameter in practice.
Though, specialized approaches may yet exist (see the discussion).



// = Implementation of Method 2

// First, we rewrite to the interarrival times. Note that the hazard of the interarrival time $S_(k) = T_(k)-T_(k-1)$ is $lambda^x (w+event(k-1) | history(k-1))$
// $
//     Qbar(k) &= commonintegral(k, tau, survivalfunction(k, s, {ell, a, d, y}) hazard(a, s, k)  \
//         & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ), s) \
//         &+ commonintegral(k, tau, survivalfunction(k, s, {ell, a, d, y}) hazard(ell, s, k) \
//             & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] ), s) \
//         &+ commonintegral(k, tau, survivalfunction(k, s, {ell, a, d, y}) hazard(y, s, k), s) \
//         &= integral_(0)^(tau-event(k-1)) exp(- sum_(x = a, ell, y, d) integral_(0)^ (s) lambda^x (w+event(k-1) | history(k-1)) upright(d) w) \
//         &times (hazard(a, event(k-1) + s, k) integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, event(k-1) + s, a, history(k)) densitytrtint(event(k-1) + s, a_k, k) nu_A (upright(d) a_k) \
//             &+ hazard(ell, event(k-1) + s, k) (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =event(k-1) + s , status(k) = ell, history(k-1)] ) \
//                 &+ hazard(y, event(k-1) + s, k) )) \
// $

// Now by using a piecewise estimator of the cumulative hazard, such as the Nelson-Aalen estimator, Cox model, or a random survival forest.
// Let $M^x_k  = {i in {1, dots, n} | D_((k),i) = x}$. Let $S_((k),i)$ be the time of the $i$'th event (ordered) in the sample.
// Then we can estimate the cumulative hazard for the interarrival times as
// $
//     hat(Lambda_(k, t)^x) (f_(k-1))= sum_(i in M_k^x) I(S_((k),i-1) < t <= S_((k), i)) hat(A)_(i,k)^x (f_(k-1))
// $
// for values $hat(A)_(i,k)^x$ that are estimated from the data. Let $c^x_k (t) = sup {i in M_k^x | T_(k,i) <= t}$.
// Then we can estimate the integrals in @eq:cuminc, for example the integral corresponding to covariate change,
// $
//     & sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (f_(k-1)))  (hat(bb(E)_P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) = t_(k-1) + S_((k),i), status(k) = ell, history(k-1) = f_(k-1)] ) \
//         &(hat(A)_(i,k)^ell - hat(A)_(i-1,k)^ell) (f_(k-1))
// $
// for given covariate history.

// We begin with an algorithm for Method 2, in which it is initially assumed that all relevant models can be fitted.

// == Surrogate/approximate modeling of the $macron(Q)$ function
// Let $K_tau$ be the maximal number of non-terminal events that occur before time $tau$.
// We suppose we are given estimators $hat(Lambda)_k (t)^x$ of the cause-specific hazard functions for the interarrival times $S_(k) = event(k) - event(k-1)$,
// which are piecewise constant. 

// 1. Let $cal(R)^y_(K, tau) = {i in {1, dots, n} | D_((K),i) in {a, ell}, T_((K), i) <= tau, D_((K), i) = y}$. 
// 2. Calculate for each $j in cal(R)_(K, tau)$, $hat(p)_(K y) = sum_(i=1)^(c^y_K (tau)) exp(- sum_(x = y, d) hat(Lambda)^x_K (cal(F)^j_(T_(K)))) (hat(Lambda)^y_K (cal(F)^j_(T_(K))) - hat(Lambda)^y_K (cal(F)^j_(T_(K-1))))$.
// 3. Use surrogate model $tilde(p)_(K y)$ for $hat(p)_(K y)$ to learn $p_(K a)$ and thus $macron(Q)_K$.

// For each event point $k = K-1, dots, 1$:
// 1. For each $j in cal(R)_(k, tau)$, calculate $hat(p)_(k y) (tau | cal(F)^j_(T_(k-1)))$ as earlier.
//    Also, calculate $hat(p)_(k a) (tau | cal(F)^j_(T_(k-1)))$ and $hat(p)_(k ell) (tau | cal(F)^j_(T_(k-1)))$
//    based on the surrogate model $tilde(Q)_(k+1)$.

// At baseline $k = 0$:
// 1. Calculate $hat(Psi)_n = 1/n sum_(i=1)^n Qbar(0) (A_0, L^i_0)$.
   
// #algorithm({
//   import algorithmic: *
//     Function("Iterative conditional expectation approach (Method 2)", {
//     For(cond: $k = K_tau, dots, 1$, {
//         Assign($cal(R)_(k, tau)$, ${i in {1, dots, n} | D_((k-1),i) in {a, ell}, T_((k-1), i) <= tau}$)
//         Comment[Obtain $hat(A)_(i,k)^x (f_j)$ for all pairs $i, j in cal(R)_(k, tau)$, $x in {a, ell, y, d}$ by regressing $(S_((k)), D_((k)) = x)$ on $history(k-1)$]
//         If(cond: $k < K_tau$, {
//             Comment[Obtain from $tilde(Q)_(k)$ predictions for each $i in cal(R)_(k, tau) inter {i | D_((k),i) = ell}$. Regress these on $event(k), status(k) = ell, history(k-1)$ to get $hat(mu) (event(k), history(k-1))$, an estimator of $bb(E)_P [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = ell, history(k-1)]$. ]
//         })
//         For(cond: $j in cal(R)_(k, tau)$, {
//             Assign($hat(p)_(k y) (tau | cal(F)^j_(T_(k-1)))$, $sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (cal(F)^j_(T_(k-1)))) (hat(A)_(i,k)^y (cal(F)^j_(T_(k-1))) - hat(A)_(i-1,k)^y (cal(F)^j_(T_(k-1))))$)
//             Assign($hat(p)_(k a) (tau | cal(F)^j_(T_(k-1)))$, $bb(1) {k < K_tau} sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (cal(F)^j_(T_(k-1)))) tilde(Q)_(k) (A_k := 1, L^i_k, D^i_k, S_(k,i,j)+ T^i_((k-1)), cal(F)^j_(T_(k-1))) (hat(A)_(i,k)^a (cal(F)^i_(T_(k-1))) - hat(A)_(i-1,k)^a (cal(F)^i_(T_(k-1))))$)
//             Assign($hat(p)_(k ell) (tau | cal(F)^j_(T_(k-1)))$, $bb(1) {k < K_tau} sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (cal(F)^j_(T_(k-1))))  hat(mu) (S_(k,i,j)+ T^i_((k-1)), cal(F)^j_(T_(k-1))) (hat(A)_(i,k)^ell (cal(F)^i_(T_(k-1))) - hat(A)_(i-1,k)^ell (cal(F)^i_(T_(k-1))))$)
//             Assign($hat(p) (tau | cal(F)^j_(T_(k-1)))$, $hat(p)_(k a) (tau | cal(F)^j_(T_(k-1))) + hat(p)_(k ell) (tau | cal(F)^j_(T_(k-1))) + hat(p)_(k y) (tau | cal(F)^j_(T_(k-1)))$)
//         })
//         Comment[Regress the predicted values $hat(p) (tau | cal(F)^j_(T_(k-1)))$ on $history(k-1)$ to get $tilde(Q)_(k-1)$; the surrogate model for $Qbar(k-1)$]
//       })
//     })
//     Cmt[From $tilde(Q)_0$ obtain predictions for each $i = 1, dots, n$ and regress on $A_0, L_0$; thereby obtaining $1/n sum_(i=1)^n hat(bb(E)_P) [Qbar(0) (A_0, L_0) | A_0 = 1, L^i_0]$ as an estimator of $Psi_tau lr((Q))$]
//     // Apply baseline regression    
//     Return[*null*]
//   })
// })
         

//*Note*: The $Qbar(k)$ have the interpretation of the
//heterogenous causal effect after $k$ events.

It is recommended to use @eq:ipcw for estimating $Qbar(k)$ instead of direct computation @eq:cuminc:
The resulting integral representing the target parameter would, in realistic settings, be incredibly highly dimensional.

//For estimators of
//the hazard that are piecewise constant, we would need to compute
//ntegrals for each unique pair of history and event times occurring
//in the sample at each event $k$, but see our discussion for an overview of
//approaches which can estimate  @eq:cuminc directly.
//On the other hand, the IPCW approach is very
//sensitive to the specification of the censoring distribution. 

// Based on this definition, we can give a simple condition for the IPCW ICE estimator to be consistent
// in the $L^2 (P)$-norm.

// #lemma[
//     Define $P_k = P |_(history(k))$ the restriction of $P$ to the $sigma$-algebra generated by the history of the first $k$ events,
//     and $P'_(k) = P |_(history(k))$ the restriction of $P$ to the $sigma(event(k), status(k)) or history(k-1)$.
//     Assume that $|| hat(nu)_(k+1) - Qbar(k+1) ||_(L^2 ( P_(k+1) )) = o_P (1)$,  $|| hat(Lambda)_(k+1)^c - Lambda_(k+1)^c ||_(L^2 (P'_(k+1))) = o_P (1)$.
//     For the censoring, we need that $hat(Lambda)^c_k$ and $Lambda^c_k$ are
//     uniformly bounded, that is $hat(Lambda)^c_k (t | f_(k-1)) <= C$ and $Lambda^c_k (t | f_(k-1))<= C$ on the
//     interval for all $t in [0, tau]$ for some constant $C>0$ and for $P$-almost all $f_(k-1)$.
//     Let $hat(P)_(k)$ denote the regression estimator of step 2 of the algorithm and assume that
//     $
//         || hat(P)_(k) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] ||_(L^2 (P_k)) = o_P (1)
//     $
//     where $macron(Z)^a_(k,tau)$ is defined as the integrand of @eq:ipcw.
//     Then,
//     $
//         || hat(nu)_(k) - Qbar(k) ||_(L^2 (P_k)) = o_P (1)
//     $ 
// ]
// #proof[
//     By the triangle inequality,
//     $
//         || hat(nu)_(k) - Qbar(k) ||_(L^2 (P_k)) &<= || hat(P)_(k) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] ||_(L^2 (P_k)) \
//             &+ || mean(P) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (S^c, hat(nu)_(k+1)) | history(k) = dot] ||_(L^2 (P_k)) \
//             &+ || mean(P) [macron(Z)^a_(k,tau) (S^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (S^c, Qbar(k+1)) | history(k) = dot] ||_(L^2 (P_k)) 
//     $
//     The first term is $o_P (1)$ by assumption. The third term is $o_P (1)$ by Jensen's inequality and by assumption. That the second term is $o_P (1)$ follows from the fact again
//     applying Jensen's inequality to see that 
//     $
//         &|| mean(P) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (S^c, hat(nu)_(k+1)) | history(k) = dot] ||_(L^2 (P_k)) \
//             &<= sqrt( integral (1/(S^c (t_(k+1) - | f_k)) - 1/(hat(S)^c (t_(k+1) - | f_(k))))^2 bb(1) {t_(k+1) <= tau, d_(k+1) in {a, ell}} hat(nu)_(k+1 )^2 (f_(k+1)) P_(k+1) (dif f_(k+1))) \
//             &<= sqrt( integral (1/(S^c (t_(k+1) - | f_k)) - 1/(hat(S)^c (t_(k+1) - | f_(k))))^2 bb(1) {t_(k+1) <= tau} P_(k+1) (dif f_(k+1))) \
//             &<= K sqrt( integral (hat(Lambda)^c_(k+1) (t_(k+1) | f_k) - Lambda^c_(k+1) (t_(k+1) | f_k))^2 bb(1) {t_(k+1) <= tau} P_(k+1) (dif f_(k+1)))
//     $ <eq:macron2>
//     This shows that the second term is $o_P (1)$. In the last equality, we used that the function $x mapsto exp(-x)$ is Lipschitz continuous (since we assume that the hazards are uniformly bounded)
//     on the set of possible values for the estimated cumulative hazard and the cumulative hazard. 
// ]


= Efficient estimation
*NOTE*: Write introduction to efficiency theory.

We want to use machine learning estimators of the nuisance parameters,
so to get inference in a non-parametric setting, we need to debias our estimate with the efficient influence function, e.g., double/debiased machine learning @chernozhukovDoubleMachineLearning2018 or
targeted minimum loss estimation (@laanTargetedMaximumLikelihood2006).
We use @eq:ipcw for censoring to derive the efficient influence function.
To do so, we introduce some additional notation and let 
$
   Qbar(k) (u  | history(k)) = p_(k a) (u | history(k-1)) + p_(k ell) (u | history(k-1)) + p_(k y) (u | history(k-1)), u < tau
$ <eq:Qbaru>
which, additionally can also be estimated with an ICE IPCW procedure (but we won't need to!).

One of the main features here is that the efficient influence function is given in terms of the martingale for the censoring process
which may be simpler computationally to implement. In an appendix, we compare
it with the efficient influence function derived in @rytgaardContinuoustimeTargetedMinimum2022.
The efficient influence function may change slightly if the censoring distribution cannot be assumed to be continuous,
but only slightly since we use the product integral
instead of the exponential function, see e.g., Theorem 8 of @gill1990survey.
This results in having to multiply by $1/(1-Delta Lambda_t^c)$ .
// in the case, where C is continuous but the others are not the product integral still factorizes into two S^c S by the trotter formula.  
// also p. 42 of ryalenPotentialOutcomes.

#theorem("Efficient influence function")[
    The efficient influence function is given by
    #text(size: 7.5pt)[$
        phi^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treat(j) = 1}) / (densitytrt(event(j), j)))^(bb(1) {status(j) = a}) 1/( product_(j=1)^(k-1) S^c (event(j)- | history(j-1))) bb(1) {status(k-1) in {ell, a}, event(k-1) < tau}  \
                & times ((macron(Z)^a_(k,tau)- Qbar(k-1)) + integral_(event(k - 1))^(tau and event(k)) (Qbar(k-1) (tau  | history(k-1))-Qbar(k-1) (u  | history(k-1))) 1/(S^c (u- | history(k-1)) S (u | history(k-1))) M_k^c (upright(d) u))\
                & +  Qbar(0) - Psi_tau (P),
    $<eq:eif>]
    where $M_k^c (t) = bb(1) {event(k-1) < t <= event(k)} (N^c (t) - Lambda^c (t | history(k-1)))$ is the martingale for the censoring process.
] <thm:eif>

#proof[
    Define (update notation)
    // inner part of Q
    $
        macron(Z)^a_(k,tau) (s, t_k, d_k, l_k, a_k, f_(k-1)) &= I(t_k <= s, d_k = ell)/(exp(-integral_(t_(k-1))^(t_k) lambda^c (s | f_(k-1)) upright(d) s)) Qbar(k)(a_(k-1), l_k, t_k, d_k, f_(k-1)) \
            &#h(1.5cm) + I(t_k <= s, d_k = a) /(exp(-integral_(t_(k-1))^(t_k) lambda^c (s | f_(k-1)) upright(d) s)) \
            &#h(2.5cm) times integral Qbar(k) (tilde(a)_k, l_(k-1), t_k, d_k, f_(k-1)) densitytrtint(t_k,a_k, k-1) nu_A (upright(d) tilde(a)_k) \
            &#h(1.5cm) +  I(t_k <= s, d_k = y)/(exp(-integral_(t_(k-1))^(t_k) lambda^c (s | f_(k-1)) upright(d) s)), s <= tau
    $ <eq:macronZ>
    and let 
    $
        Qbar(k-1) (s) = mean(P) [macron(Z)^a_(k,s) (tau, event(k), status(k), covariate(k), treat(k), history(k-1)) | history(k-1)], s <= tau
    $
    We compute the efficient influence function by taking the Gateaux derivative of the above with respect to $P$,
    by discretizing the time. Note that this is not a rigorous argument showing that the
    efficient influence function is given by @eq:eif. To formally prove that is
    the efficient influence function, we would have to compute the pathwise derivative
    of the target parameter along parametric submodels with a given score function. 
    We will use two well-known "results" for the efficient influence function. 
    $
        &partial / (partial epsilon) integral_(event(k-1))^t lambda^x_epsilon (s | history(k-1)) upright(d) s \
            &= (delta_(history(k-1)) (f_(k-1)))/P(history(k-1) = f_(k-1)) integral_(event(k-1))^t 1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^x (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(x, s, k-1) upright(d) s)
    $
    and
    $
        partial / (partial epsilon) lr(mean((1-epsilon)P + epsilon delta_((Y, X))) [Y | X = x] bar.v)_(epsilon = 0) = (delta_(X) (x)) / P(X = x) (Y - mean(P) [Y | X = x])
    $
    We will recursively calculate the derivative,
    $
        partial / (partial epsilon) lr(macron(Q)^(a,epsilon)_(k - 1, tau) (a_(k-1), l_(k-1), t_(t-1), d_(k-1), f_(k-2)) ((1-epsilon)P + epsilon delta_(history(k-1))) bar.v)_(epsilon = 0)
    $
    where we have introduced the notation for the dependency on $P$.
    Then, taking the Gateaux derivative of the above yields,
    $
        & partial / (partial epsilon) lr(macron(Q)^(a,epsilon)_(k - 1, tau) (a_(k-1), l_(k-1), t_(t-1), d_(k-1), f_(k-2)) ((1-epsilon)P + epsilon delta_(history(k-1))) bar.v)_(epsilon = 0) \
            &= delta_(history(k-1) (f_(k-1)))/P(history(k-1) = f_(k-1))  (macron(Z)^a_(k,tau) - Qbar(k-1) (tau, history(k-1)) + \            
            &+ integral_(event(k-1))^(tau) macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) integral_(event(k-1))^(t_k) 1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s) \
            &#h(1.5cm) P_((event(k), status(k), covariate(k), treat(k))) (upright(d) t_k, upright(d) d_k, upright(d) l_k, upright(d) a_k | history(k-1) = f_(k-1))) \
            &+ integral_(event(k-1))^(tau) (I(t_k <= tau, d_(k) in {a, ell})/(exp(-integral_(event(k-1))^(t_(k)) lambda^c (s | f_(k-1)) upright(d) s)) dot ((densitytrtint(t_(k), a_(k), k-1)) / (densitytrt(t_(k), k-1)))^(I(d_(k) = a)) partial / (partial epsilon) lr(macron(Q)^(a,epsilon)_(k - 1, tau) (a_(k), l_(k),t_(k), d_(k), f_(k-1)) ((1-epsilon)P + epsilon delta_(history(k))) bar.v)_(epsilon = 0) \
            &#h(1.5cm) P_((event(k), status(k), covariate(k), treat(k))) (upright(d) t_k, upright(d) d_k, upright(d) l_k, upright(d) a_k | history(k-1) = f_(k-1)) 
    $
    Now note for the second term, we can write
    $
        &integral_(event(k-1))^(tau) macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) integral_(event(k-1))^(t_k) 1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s) \
            &#h(1.5cm) P_((event(k), status(k), covariate(k), treat(k))) (upright(d) t_k, upright(d) d_k, upright(d) l_k, upright(d) a_k | history(k-1) = f_(k-1))) \
        &= integral_(event(k-1))^(tau) integral_(s)^tau macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) P_((event(k), status(k), covariate(k), treat(k))) (upright(d) t_k, upright(d) d_k, upright(d) l_k, upright(d) a_k | history(k-1) = f_(k-1)) \
            &#h(1.5cm)1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s)) \
            &= integral_(event(k-1))^(tau) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
                &#h(1.5cm)1/exp(-sum_(x=a,ell,c,d,y) integral_(event(k-1))^s hazard(x, s, k-1) upright(d) s) (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s)) \
    $
    by an exchange of integerals. Combining the results iteratively gives the result.
]
//For now, we recommend using the one step estimator and not the TMLE because the martingales are computationally intensive to estimate.
//This means that multiple TMLE updates may not be a good idea. 

== Paired ICE IPCW one-step estimator

In this section, we provide a special procedure for the purpose of one-step estimation.
Though the present section is stated in the context one-step estimation,
a targeted minimum loss estimator (TMLE) can be obtained by very similar considerations. //using the same procedure, fluctuating the $Q$ and $S^c$-estimates.
Recall that the efficient influence function in @eq:eif includes a censoring martingale.
To estimate this martingale, we would need to have estimators of $Qbar(k) (t)$ (defined in @eq:Qbaru) at a sufficiently dense grid of time points $t$.
Unfortunately, the event-specific cause-specific hazards $hat(Lambda)_(k)^x$ cannot readily be used to estimate $Qbar(k) (t)$
directly due to the aforementioned high dimensionality of integrals. 
The IPCW approach we have given in @alg:ipcwice also would be prohibitively computationally expensive (at the very least if we use flexible machine learning estimators). 
//Regression with a multivariate outcome can accommodate this to some extent. 
//Another issue altogether is that it does not explicitly give conditions on the remainder since we will integrate with respect to $Qbar(k)$.
Instead, we split up the estimation the estimation into two parts for $Qbar(k)$.
For each $k$, the procedure constructs two new estimators of $Qbar(k)$:
1. $hat(nu)_(k, tau) (history(k))$ which is obtained the same way as in @alg:ipcwice. 
2. First obtain the estimates $tilde(nu)_(k,tau)$ by regressing $hat(R)_(k+1)$ on $(event(k), status(k), treat(k), history(k-1))$ (i.e., we do not include the latest covariate value).
   Given cause-specific estimators $hat(Lambda)_(k+1)^x$ for $x=a,l,d,y$, we estimate
       $Qbar(k) (t, history(k))$ by
       $
           hat(nu)^*_(k,tau) (t | history(k)) &= integral_(0)^(t-event(k)) prodint2(s, 0, u-event(k)) (1-sum_(x=a,l,d,y) hat(Lambda)_(k+1)^x (d s | history(k))
           [hat(Lambda)_(k+1)^y (d u | history(k)) \
               &+ tilde(nu)_(k+1,tau) (u + event(k), a, 1, history(k)) hat(Lambda)_(k+1)^a (d u |  history(k))) \
               &+ tilde(nu)_(k+1,tau) (u + event(k), ell, treat(k), history(k)) hat(Lambda)_(k+1)^ell (d u |  history(k))]
       $
   on the interevent level as we explained in step 1 of @alg:ipcwice.
Given also estimators of the propensity scores, we can estimate the efficient influence function as:
$
    phi^* (hat(P)_n^*) &= (bb(1) {treat(0) = 1})/ (hat(pi)_0 (L(0))) product_(j = 1)^(k-1) ((bb(1) {treat(j) = 1}) / (hat(pi) (event(j), treat(j), history(j-1))))^(bb(1) {status(j) = a}) 1/( product_(j=1)^(k-1) hat(S)^c (event(j)- | history(j-1))) bb(1) {status(k-1) in {ell, a}, event(k-1) < tau}  \
        & times (macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k,tau))- hat(nu)_(k-1, tau) (history(k-1)) + integral_(event(k - 1))^(tau and event(k)) (hat(nu)^*_(k-1) (tau | history(k-1)) - hat(nu)^*_(k-1, tau) (u |history(k-1))) 1/(hat(S)^c (u- | history(k-1)) hat(S) (u | history(k-1))) M_k^c (upright(d) u)) \
        & +  hat(nu)_(0, tau) (1, history(0)) - bb(P)_n hat(nu)_(0, tau) (1, dot)
$
The resulting one-step estimator is given by
$
    hat(Psi)_n = bb(P)_n hat(nu)_(0, tau) (1, dot) + bb(P)_n phi^* (hat(P)_n^*)
$
Under regularity conditions and empirical process, the one-step estimator is asymptotically linear
and locally efficient.
Conditions for the remainder term are given in @thm:remainder.
Conditions for the empirical process term are not stated here _yet_.

We have the following rate result for $hat(nu)^*_(k,tau)$
which may be used in conjunction with @thm:remainder.

Let $|| dot ||_(L^2 (P)) $ denote the $L^2 (P)$-norm,
that is
$
    || f ||_(L^2 (P)) &= sqrt(mean(P) [f^2 (X)]) = sqrt(integral f^2 (x) P(d x)).
$
#lemma[
    Let $macron(Q)^(-L)_k = mean(P) [Qbar(k) | treat(k), event(k), status(k), history(k-1)]$.
    Assume that $|| tilde(nu)^*_(k+1) - macron(Q)^(-L)_(k+1)  ||_(L^2 (P)) = o_P (1)$.
    If the estimators for the cause-specific hazards for the event times
    converge, that is
        $
            sqrt(integral integral_(t_(k-1))^tau (lambda_(k+1)^x (t | f_(k)) - hat(lambda)_(k+1)^x (t | f_(k)))^2 d t P_(history(k)) (d f_(k))) = o_P (1)
        $
    for $ x= a, ell, d, y$.
    Then for the derivatives of $hat(nu)^*_(k,tau)$ and $Qbar(k)$, we have
    $
        || hat(nu)^(*,')_(k,tau) - Qbar(k)' ||_(L^2 (P_k^*)) = o_P (1)
    $
    where $P_k^* = m times.circle P|_(history(k))$ and $m$ is the Lebesgue measure on the interval $[0,tau]$.
    // integrate over time
]
#proof[
    *Somewhat incomplete*.
        By the triangle inequality,
        $
            || hat(nu)^(*,')_(k,tau)  - Qbar(k)' ||_(L^2 (P)) &<= sqrt( integral integral_(t_(k))^tau (hat(S)_(k+1) (t|f_k) hat(lambda)_(k+1)^y (t | f_(k)) - S_(k+1) (t|f_k)lambda_(k+1)^y (t | f_(k)))^2 d t P_(history(k)) (d f_(k))) \
                &+sqrt( integral integral_(t_(k))^tau (hat(lambda)_(k+1)^a (t | f_(k)) hat(S)_(k+1) (t|f_k)  - S_(k+1) (t|f_k) lambda_(k+1)^a (t | f_(k)) )^2 (tilde(nu) (1, t, a, f_k))^2 d t P_(history(k)) (d f_(k))) \
                &+sqrt( integral integral_(t_(k))^tau (hat(lambda)_(k+1)^ell (t | f_(k)) hat(S)_(k+1) (t|f_k)  - S_(k+1) (t|f_k) lambda_(k+1)^ell (t | f_(k)) )^2 (tilde(nu) (a_(k-1), t, a, f_k))^2 d t P_(history(k)) (d f_(k))) \
                &+ sqrt( integral integral_(t_(k))^tau (tilde(nu)^*_(k+1,tau) (t, dots) - macron(Q)^(-L)_(k+1) (t, dots))^2  (sum_(x=a,l,y) S_(k+1) (t|f_k) lambda_(k+1)^x (t | f_(k)) ) d t P_(history(k-1)) (d f_(k))) \
        $
    The last term is $o_P (1)$ by assumption. By bounding $tilde(nu)$, the first three terms are then also $o_P (1)$.
    By i.e., noting that the mapping $(x,y) mapsto x exp(-(x+y))$ is Lipschitz continuous and uniformly bounded (under additional boundedness conditions on the hazards),
    we see that the conditions on the hazards are sufficient to show that the first three terms are $o_P (1)$.
]

== Remainder term
We now consider the efficient influence function, occuring in the remainder term.
The following result shows that we can separate the estimation of the martingale term
and the outcome term in the efficient influence function. 

#theorem("Remainder term")[
    The remainder term $R_2 = Psi_tau (P) - Psi_tau (P_0) + mean(P_0) [phi^* (P)]$ is given by
    $
        R_2 = sum_(k=1)^K integral bb(1) {t_1 < dots < t_(k) < tau} 
        product_(j = 0)^(k-2) ((pi_(0,j) (t_k, f^(bold(1))_(j-1))) / (pi_(j) (t_k, f_(j-1)^(bold(1)))))^(bb(1) {d_j = a}) (product_(j=1)^(k-1) S_0^c (t_j- | f^(bold(1))_(j-1)))/( product_(j=1)^(k-1) S^c (t_j- | f_(j-1)^(bold(1)))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} z_k (f^(bold(1))_(j-1)) P_(cal(F)_(T_(k))) (d f_(k)),
    $
    where
    $
        z_k (history(k)) &= (((pi_(k-1,0) (event(k), history(k-1)))/ (pi_(k-1) (event(k), history(k-1))))^(bb(1) {status(k) = a})-1) (Qbar(k-1) (history(k-1))- nu_(k-1, tau) (history(k-1))) \
        &+((pi_(k-1,0) (event(k), history(k-1)))/ (pi_(k-1) (event(k), history(k-1))))^(bb(1) {status(k) = a})integral_(event(k - 1))^(tau) ((S_0^c (u | history(k-1))) / (S^c (u | history(k-1)))-1) (Qbar(k-1) (d u | history(k-1)) - nu^*_(k-1, tau) (d u |history(k-1))) \
            &+((pi_(k-1,0) (event(k), history(k-1)))/ (pi_(k-1) (event(k), history(k-1))))^(bb(1) {status(k) = a}) integral_(event(k - 1))^(tau) V_k (u, history(k-1)) nu^*_(k-1, tau) (d u |history(k-1)),
    $
    and $V_k (u, history(k)) = integral_(event(k-1))^u ((S_0 (s | history(k-1))) / (S (s | history(k-1))) - 1)  (S_0^c (s- | history(k-1)))/(S^c (s- | history(k-1))) (Lambda^c_(k,0) (d s | history(k-1)) - Lambda^c (d s | history(k-1)))$.
    Here $f^(bold(1))_(j)$ simply means that we insert 1 into every place where we have $a_i, i = 1, dots, j$ in $f_(j)$.
    *NOTE*: We define the empty product to be 1 and $pi_(0) (event(0), history(-1)) = pi_(0) (covariate(0))$ (and $pi_(0,0)$).
] <thm:remainder>
#proof[
*NOTE*: We should write $f^(bold(1))_(j)$ most places instead of $f_(j)$.    
*Sketch*: First define
$
    phi_k^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) product_(j = 1)^(k-1) ((bb(1) {treat(j) = 1}) / (densitytrt(event(j), j)))^(bb(1) {status(j) = a}) 1/( product_(j=1)^(k-1) S^c (event(j)- | history(j-1))) bb(1) {status(k-1) in {ell, a}, event(k-1) < tau}  \
        & times ((macron(Z)^a_(k,tau)- nu_(k-1)) + integral_(event(k - 1))^(tau and event(k)) (nu^*_(k-1) (tau) - nu^*_(k-1) (u) ) 1/(S^c (u- | history(k-1)) S (u | history(k-1))) M_k^c (upright(d) u)) \
$
    for $k>0$ and define $phi_0^* (P) = nu_(0) (covariate(0)) - Psi_tau (P)$, so that
$
    phi^* (P) = sum_(k=0)^(K) phi_k^* (P)
$
Also note that
    $
        mean(P_0) [phi_0^* (P)] + Psi_tau (P) - Psi_tau (P_0) =  mean(P_0)[nu_(0) (covariate(0)) - Qbar(0) (covariate(0))].
    $ <eq:cancelterm0>
Apply the law of iterated expectation to the efficient influence function in @eq:eif to get
$
mean(P_0) [phi_k^* (P)] &= integral bb(1) {t_1 < dots < t_(k-1) < tau} (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k-1) ((pi_(0,j) (t_k, f_(j-1))) / (pi_(j) (t_k, f_(j-1))))^(bb(1) {d_j = a}) (product_(j=1)^(k-1) S_0^c (t_j- | f_(j-1)))/( product_(j=1)^(k-1) S^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} \
    & times (mean(P) [h_k (history(k)) | history(k-1) = f_(k-1)] P_(history(k-1)) (d f_(k-1))
$          
where
$
    h_k (history(k)) = macron(Z)^a_(k,tau)- nu_(k-1) + integral_(event(k - 1))^(tau and event(k)) (nu^*_(k-1) (tau  | history(k-1))-nu^*_(k-1) (u  | history(k-1))) 1/(S^c (u- | history(k-1)) S (u | history(k-1))) M_k^c (upright(d) u).
$
Now note that
$
    & mean(P_0) [h_k (history(k)) | history(k-1)] \
        &= mean(P_0) [macron(Z)^a_(k,tau) (S^c, nu_(k)) | history(k-1)] - nu_(k-1, tau) (history(k-1)) \
        &+ mean(P_0) [ integral_(event(k - 1))^(tau and event(k)) (nu^*_(k-1) (tau | history(k-1)) - nu^*_(k-1, tau) (u |history(k-1))) 1/(S^c (u- | history(k-1)) S (u | history(k-1))) M_k^c (upright(d) u)) | history(k-1)] \
        &= mean(P_0) [macron(Z)^a_(k,tau) (S_0^c,  Qbar(k))) | history(k-1)] - nu_(k-1, tau) (history(k-1)) \
            &+ mean(P_0) [macron(Z)^a_(k,tau) (S^c, nu_(k)) | history(k-1)]- mean(P_0) [macron(Z)^a_(k,tau) (S^c, Qbar(k)) | history(k-1)] \
            &+mean(P_0) [macron(Z)^a_(k,tau) (S^c, Qbar(k)) | history(k-1)] - mean(P_0) [macron(Z)^a_(k,tau) (S_0^c,  Qbar(k))) | history(k-1)] \
            &+ integral_(event(k - 1))^(tau) (nu^*_(k-1) (tau | history(k-1)) - nu^*_(k-1, tau) (u |history(k-1))) (S_0^c (u- | history(k-1)) S_0 (u | history(k-1)))/(S^c (u- | history(k-1)) S (u | history(k-1))) (Lambda^c_(k,0) (d u | history(k-1)) - Lambda^c (d u | history(k-1)))
$
by a martingale argument. Noting that,
$
    &mean(P_0) [ integral_(event(k - 1))^(tau and event(k)) (nu^*_(k-1) (tau | history(k-1)) - nu^*_(k-1, tau) (u |history(k-1))) 1/(S^c (u- | history(k-1)) S (u | history(k-1))) M_k^c (upright(d) u) | history(k-1)] \
        &=integral_(event(k - 1))^(tau) (nu^*_(k-1) (tau | history(k-1)) - nu^*_(k-1, tau) (u |history(k-1))) (S_0^c (u- | history(k-1)) S_0 (u | history(k-1)))/(S^c (u- | history(k-1)) S (u | history(k-1))) (Lambda^c_(k,0) (d u | history(k-1)) - Lambda^c (d u | history(k-1))) \
        &=integral_(event(k - 1))^(tau) integral_(event(k-1))^u (S_0^c (s- | history(k-1)) S_0 (s | history(k-1)))/(S^c (s- | history(k-1)) S (s | history(k-1))) (Lambda^c_(k,0) (d s | history(k-1)) - Lambda^c (d s | history(k-1))) (nu^*_(k-1, tau) (d u |history(k-1))) \
        &=integral_(event(k - 1))^(tau) integral_(event(k-1))^u ((S_0 (s | history(k-1))) / (S (s | history(k-1))) - 1)  (S_0^c (s- | history(k-1)))/(S^c (s- | history(k-1))) (Lambda^c_(k,0) (d s | history(k-1)) - Lambda^c (d s | history(k-1))) (nu^*_(k-1, tau) (d u |history(k-1))) \
        &+integral_(event(k - 1))^(tau) integral_(event(k-1))^u ((S_0^c (s- | history(k-1))) / (S^c (s- | history(k-1)))) (Lambda^c_(k,0) (d s | history(k-1)) - Lambda^c (d s | history(k-1))) (nu^*_(k-1, tau) (d u |history(k-1))) \
        &=integral_(event(k - 1))^(tau) integral_(event(k-1))^u ((S_0 (s | history(k-1))) / (S (s | history(k-1))) - 1)  (S_0^c (s- | history(k-1)))/(S^c (s- | history(k-1))) (Lambda^c_(k,0) (d s | history(k-1)) - Lambda^c (d s | history(k-1))) (nu^*_(k-1, tau) (d u |history(k-1))) \
        &-integral_(event(k - 1))^(tau) ((S_0^c (u | history(k-1))) / (S^c (u | history(k-1)))-1) (nu^*_(k-1, tau) (d u |history(k-1)))
$
    where we apply the Duhamel equation in the second last equality, 
it follows that
$
    & mean(P_0) [h_k (history(k)) | history(k-1)] \
        &=mean(P_0) [macron(Z)^a_(k,tau) (S_0^c,  Qbar(k))) | history(k-1)] - nu_(k-1, tau) (history(k-1)) \
        &+ mean(P_0) [macron(Z)^a_(k,tau) (S^c, nu_(k)) | history(k-1)]- mean(P_0) [macron(Z)^a_(k,tau) (S^c, Qbar(k)) | history(k-1)] \
        &+integral_(event(k - 1))^(tau) ((S_0^c (u | history(k-1))) / (S^c (u | history(k-1)))-1) (nu^*_(k-1, tau) (d u |history(k-1)) - Qbar(k-1) (d u | history(k-1))) \
        &+integral_(event(k - 1))^(tau) integral_(event(k-1))^u ((S_0 (s | history(k-1))) / (S (s | history(k-1))) - 1)  (S_0^c (s- | history(k-1)))/(S^c (s- | history(k-1))) (Lambda^c_(k,0) (d s | history(k-1)) - Lambda^c (d s | history(k-1))) (nu^*_(k-1, tau) (d u |history(k-1))) \
$
Since also
$
    &integral bb(1) {t_1 < dots < t_(k) < tau} (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k) ((pi_(0,j) (t_j, f_(j-1))) / (pi_(j) (t_j, f_(j-1))))^(bb(1) {d_j = a}) (product_(j=1)^(k) S_0^c (t_j- | f_(j-1)))/( product_(j=1)^(k) S^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k) in {ell, a}} \
        & qquad times (mean(P_0) [macron(Z)^a_(k+1,tau) (S_0^c,  Qbar(k+1)) | history(k) = f_k] - nu_(k, tau) (f_k)) P_(history(k)) (d f_(k)) \
        &+integral bb(1) {t_1 < dots < t_(k-1) < tau} (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k-1) ((pi_(0,j) (t_k, f_(j-1))) / (pi_(j) (t_k, f_(j-1))))^(bb(1) {d_j = a}) (product_(j=1)^(k-1) S_0^c (t_j- | f_(j-1)))/( product_(j=1)^(k-1) S^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} \
        &qquad times mean(P_0) [macron(Z)^a_(k,tau) (S^c, nu_(k)) | history(k-1) = f_(k-1)]- mean(P_0) [macron(Z)^a_(k,tau) (S^c, Qbar(k)) | history(k-1) = f_(k-1)] P (history(k-1)) (d f_(k-1)) \
        &=integral bb(1) {t_1 < dots < t_(k) < tau} (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k) ((pi_(0,j) (t_j, f_(j-1))) / (pi_(j) (t_j, f_(j-1))))^(bb(1) {d_j = a}) (product_(j=1)^(k) S_0^c (t_j- | f_(j-1)))/( product_(j=1)^(k) S^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k) in {ell, a}} \
        & qquad times (Qbar(k) (f_k) - nu_(k, tau) (f_k)) P_(history(k)) (d f_(k)) \
        &+integral bb(1) {t_1 < dots < t_(k-1) < tau} (pi_(0,0) (l_0))/ (pi_0 (l_0))
    product_(j = 1)^(k-1) ((pi_(0,j) (t_k, f_(j-1))) / (pi_(j) (t_k, f_(j-1))))^(bb(1) {d_j = a}) (product_(j=1)^(k-1) S_0^c (t_j- | f_(j-1)))/( product_(j=1)^(k-1) S^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k-1) in {ell, a}} \
        &quad integral bb(1) {t_k < tau} (S_0^c (t_k- | f_(k-1)))/( S^c (t_k- | f_(k-1))) \
        &qquad times sum_(d_k=a, ell) (nu_(k) (t_k, d_k, g_k (a_k, d_k, f_(k-1)), l_k, f_(k-1)) - Qbar(k) (t_k, d_k, g_k (a_k, d_k, f_(k-1)), l_k, f_(k-1)))
        P_(event(k), status(k), covariate(k) | history(k-1)) (d f_k | f_(k-1)) P (history(k-1)) (d f_(k-1)) \
        &=integral bb(1) {t_1 < dots < t_(k) < tau} (pi_(0,0) (l_0))/ (pi_0 (l_0))
        product_(j = 1)^(k-1) ((pi_(0,j) (t_j, f_(k-1))) / (pi_(j) (t_j, f_(j-1))))^(bb(1) {d_k = a}) (((pi_(0,k) (k_j, f_(k-1))) / (pi_(k) (t_k, f_(k-1))))^(bb(1) {d_k = a})-1) (product_(j=1)^(k) S_0^c (t_j- | f_(j-1)))/( product_(j=1)^(k) S^c (t_j- | f_(j-1))) bb(1) {d_1 in {ell, a}, dots, d_(k) in {ell, a}} \
        & qquad times (Qbar(k) (f_k) - nu_(k, tau) (f_k)) P_(history(k)) (d f_(k))
$ <eq:canceltermk>  
    where we set $g_k (a_k, d_k, f_(k-1)) = 1$ for $k>1$.
    By combining @eq:cancelterm0 and @eq:canceltermk, we are done.  
]
Note that by the triangle inequality
$
    &|integral_(event(k - 1))^(tau) integral_(event(k-1))^u ((S_0 (s | history(k-1))) / (S (s | history(k-1))) - 1)  (S_0^c (s- | history(k-1)))/(S^c (s- | history(k-1))) (Lambda^c_(k,0) (d s | history(k-1)) - Lambda^c (d s | history(k-1))) (nu^*_(k-1, tau) (d u |history(k-1)))| \
        &<= nu^*_(k-1, tau) (tau) sup_(u in (event(k-1), tau)) | integral_(event(k-1))^u ((S_0 (s | history(k-1))) / (S (s | history(k-1))) - 1)  (S_0^c (s- | history(k-1)))/(S^c (s- | history(k-1))) (Lambda^c_(k,0) (d s | history(k-1)) - Lambda^c (d s | history(k-1)))| \
$

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

Other methods provide means of estimating the cumulative intensity $Lambda^x$ directly instead of splitting it up into $K$ separate parameters.
There exist only a few methods for estimating the cumulative intensity $Lambda^x$ directly (see @liguoriModelingEventsInteractions2023 for neural network-based methods and
@weissForestBasedPointProcess2013 for a forest-based method).

Alternatively, we can use temporal difference learning to avoid iterative estimation of $Qbar(k)$ altogether #citep(<shirakawaLongitudinalTargetedMinimum2024>).

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
// for the original estimator for $phi_tau^*(P) (K_lim)$

A potential other issue with the estimation of the nuisance parameters are that the history is high dimensional.
This may yield issues with regression-based methods. If we adopt a TMLE approach, we may be able to use collaborative TMLE #citep(<van2010collaborative>)
to deal with the high dimensionality of the history.

There is also the possibility for functional efficient estimation using the entire interventional cumulative incidence curve
as our target parameter. There exist some methods for baseline interventions in survival analysis
(@onesteptmle @westling2024inference).

// Here are some ideas:

// - *Ad-hoc*: Use Early-stopping cross-validation described as follows:
//   First fit models with no covariates.
//   Then we fit a model with the covariates from the last event.
//   Determine if this is improves model fit via cross-validation and then we move on to the two latest changes and so on.
//   Stop when the model fit does not improve. Theorem 2 of @schulerSelectivelyAdaptiveLasso2022 states that the convergence rates for an empirical risk minimizer are preserved.
//   CTMLE also does something very similar #citep(<van2010collaborative>).
//   This way, we may only select variables that are important in the specification of the treatment and outcome mechanism.


//Interestingly, $integral Qbar(0) (a, covariate(0)) nu_A (upright(d) a)$ is a heterogenous causal effect.
//an we estimate heterogenous causal effects in this way?

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
    //    Here $#scale(160%)[$pi$]$ denotes the product integral #citep(<gill1990survey>). 
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

// == Remainder term for $K = 2$
// //May be useful to consider the estimator as an empirical process, i.e., see Anders PhD first manuscript with Nelson-Aalen.

// Taking the mean of the EIF with respect to $P_0$ gives

// $
//     mean(P_0) [phi_tau^*(P)] &=mean(P_0) [ sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), treat(j), j-1)))^(I(status(j) = a)) (I (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) upright(d) s)) [ \
//         &integral_(event(k-1))^tau S_0(u |history(k-1))(S^c_0(u |history(k-1))) /(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)- B_(k-1) (u)) (Lambda_(k,0)^a (d u) - Lambda_(k)^a (d u)) \
//             &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] - B_(k-1) (u)) (Lambda_(k,0)^ell (d u) - Lambda_(k)^ell (d u)) \
//         &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (1 - B_(k-1) (u)) (Lambda_(k,0)^y (d u) - Lambda_(k)^y (d u)) +integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) -B_(k-1) (u) (Lambda_(k,0)^d (d u) - Lambda_(k)^d (d u)) \
//         &+  bb(1) {k < K}
//             integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1)))( mean(P_0) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = u , status(k) = ell, history(k-1)] \
//                 &#h(1.5cm) - mean(P) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = u, status(k) = ell, history(k-1)] ) Lambda_(k,0)^c (d u) ]]\
//         &+ mean(P_0) [integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (upright(d) a)]- Psi_tau (P) 
// $
// We need to calculate
// $
//     R_2(P,P_0) &= Psi_tau (P)-Psi_tau (P_0) + P_0 (phi_(tau)^*(P)) \
//         &=mean(P_0) [ sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), treat(j), j-1)))^(I(status(j) = a)) (I (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) upright(d) s)) [ \
//         &integral_(event(k-1))^tau S_0(u |history(k-1))(S^c_0(u |history(k-1))) /(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)- B_(k-1) (u)) (Lambda_(k,0)^a (d u) - Lambda_(k)^a (d u)) \
//             &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] - B_(k-1) (u)) (Lambda_(k,0)^ell (d u) - Lambda_(k)^ell (d u)) \
//         &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (1 - B_(k-1) (u)) (Lambda_(k,0)^y (d u) - Lambda_(k)^y (d u)) +integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) -B_(k-1) (u) (Lambda_(k,0)^d (d u) - Lambda_(k)^d (d u)) \
//         &+  bb(1) {k < K}
//             integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1)))( mean(P_0) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = u , status(k) = ell, history(k-1)] \
//                 &#h(1.5cm) - mean(P) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = u, status(k) = ell, history(k-1)] ) Lambda_(k,0)^ell (d u) ]]\
//         &+ mean(P_0) [integral Qbar(1) (a, covariate(0))- Qbar(1)_0 (a, covariate(0)) densitytrtint(0, a, 0) nu_A (upright(d) a)]
// $
// By the Duhamel equation,
// $
//     & Qbar(1) (a, covariate(0))- Qbar(1)_0 \
//         &= S_0(s) ("bla"- "bla"_0) + (S (s) - S_0(s)) "bla" \
//         &= S_0(s) ("bla" Q - "bla"_0 Q + "bla"_0 Q - "bla"_0 Q_0)- integral S_0 B_(k-1) sum_x (Lambda_(0,x) - Lambda_x) 
// $
// The second term gives that we can ignore $B_k$:
// $
//     & integral_(event(k-1))^tau S_0(u |history(k-1))(S^c_0(u |history(k-1))) /(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)) (Lambda_(k,0)^a (d u) - Lambda_(k)^a (d u)) \
//             &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) (Lambda_(k,0)^ell (d u) - Lambda_(k)^ell (d u)) \
//         &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (Lambda_(k,0)^y (d u) - Lambda_(k)^y (d u)) \
//         &+  bb(1) {k < K}
//             integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1)))( mean(P_0) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = u , status(k) = ell, history(k-1)] \
//                 &#h(1.5cm) - mean(P) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = u, status(k) = ell, history(k-1)] ) Lambda_(k,0)^ell (d u) \
//         &=integral_(event(k-1))^tau S_0(u |history(k-1))(S^c_0(u |history(k-1))) /(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)) (Lambda_(k,0)^a (d u) - Lambda_(k)^a (d u)) \
//             &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) (- Lambda_(k)^ell (d u)) \
//         &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (Lambda_(k,0)^y (d u) - Lambda_(k)^y (d u)) \
//         &+  bb(1) {k < K}
//             integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1)))( mean(P_0) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = u , status(k) = ell, history(k-1)] ) Lambda_(k,0)^ell (d u) \
//         &=integral_(event(k-1))^tau S_0(u |history(k-1))(S^c_0(u |history(k-1))) /(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k)_0 (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)) Lambda_(k,0)^a (d u) \
//         & -integral_(event(k-1))^tau S_0(u |history(k-1))(S^c_0(u |history(k-1))) /(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)) Lambda_(k)^a (d u)\
//         &+integral_(event(k-1))^tau S_0(u |history(k-1))(S^c_0(u |history(k-1))) /(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) - Qbar(k)_0 (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)) Lambda_(k,0)^a (d u) \
//         &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (mean(P_0) [Qbar(k) . | event(k) =s , status(k) = ell, history(k-1)]- mean(P_0) [Qbar(k)_0 . | event(k) =s , status(k) = ell, history(k-1)]) Lambda_(k,0)^ell (d u) \
//         &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (mean(P_0) [Qbar(k)_0 (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) Lambda_(k,0)^ell (d u) \
//             &-integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) Lambda_(k)^ell (d u) \
//         &+integral_(event(k-1))^tau S_0(u |history(k-1)) (S^c_0(u |history(k-1)))/(S^c (u | history(k-1))) (Lambda_(k,0)^y (d u) - Lambda_(k)^y (d u))
// $
// Adding the first term together in the sum with the last term, we have
// $
//     mean(P_0) [phi_tau^*(P)] &=mean(P^*_0) [
//         integral_(0)^tau S_0(u |history(0)) ((pi_0 (L(0))) / (pi(L(0))) (S^c_0(u |history(0))) /(S^c (u | history(0)))-1) (Qbar(0)_0 (d s, history(0)) - Qbar(0) (d s, history(0)))  \
//             &+integral_0^tau S_0(u |history(0)) (pi_0 (L(0))) / (pi(L(0))) (S^c_0(u |history(0))) /(S^c (u | history(0))) (sum_(x=a,ell) mean(P^*_0)  [Qbar(1) - Qbar(1)_0 | event(1) = s, status(1)= x, history(0)] Lambda_(1,0)^x (d u) )] \
//         &= mean(P^*_0) [integral_(0)^tau S_0(u |history(0)) ((pi_0 (L(0))) / (pi(L(0))) (S^c_0(u |history(0))) /(S^c (u | history(0)))-1) (Qbar(0)_0 (d s, history(0)) - Qbar(0) (d s, history(0))) ] \
//         &+mean(P^*_0) [integral_(event(k-1))^tau S_0(u |history(k-1)) (pi_0 (L(0))) / (pi(L(0))) (S^c_0(u |history(k-1))) /(S^c (u | history(k-1))) \
//             &times (sum_(x=a,ell) mean(P^*_0)  [integral_(0)^tau S_0(s |history(1)) ((pi_(1,0) (event(1), treat(1), history(0))) / (pi_(1) (event(1), treat(1), history(0))) (S^c_0(s |history(1))) /(S^c (u | history(1)))-1) (Qbar(1)_0 (d s, history(1)) - Qbar(1) (d s, history(1))) | event(1) = u, status(1)= x, history(0)] Lambda_(1,0)^x (d u) )
// $

== Comparison with the EIF in @rytgaardContinuoustimeTargetedMinimum2022
Let $B_(k-1) (u) = (Qbar(k-1)(tau) -Qbar(k-1)(u)) 1/exp(-sum_(x=a,ell,d,y) integral_(event(k-1))^u hazard(x, w, k-1) upright(d) w)$
and $S (u | history(k-1)) = exp(-sum_(x=a,ell,d,y) integral_(event(k-1))^u hazard(x, w, k-1) upright(d) w)$ and $S^c (u | history(k-1)) = exp(- integral_(event(k-1))^u hazard(c, w, k-1) upright(d) w)$.
We claim that the efficient influence function can also be written as:
$
    phi_tau^*(P) &= sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), j-1)))^(I(status(j) = a)) (I (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) upright(d) s)) [ \
        &integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)- B_(k-1) (u)) M_k^(a) (d u) \
         &+integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] - B_(k-1) (u)) M_k^(ell) (d u) \
         &+integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) (1 - B_(k-1) (u)) M_k^(y) (d u) +integral_(event(k-1))^tau 1/(S^c (u | history(k-1)))(0 - B_(k-1) (u)) M_k^(d) (d u) \
        &+  1/(S^c (event(k) | history(k-1))) I(event(k) <= tau, status(k) = ell, k < K)( Qbar(k) (covariate(k), treat(k-1), event(k), ell, history(k-1)) \
                            &#h(1.5cm) - mean(P) [Qbar(k-1) (covariate(k), treat(k-1), tilde(event(k)), status(k), history(k-1)) | tilde(event(k)) = event(k) , status(k) = ell, history(k-1)] )]\
                        &+ integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (upright(d) a)- Psi_tau (P) 
$

We find immediately that

$
    phi_tau^*(P) &= sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), j-1)))^(I(status(j) = a)) (I (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) upright(d) s)) [ \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k)) Lambda_k^(a) (d u) \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) Lambda_k^(ell) (d u) \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (1) Lambda_k^(y) (d u) -integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)))(0) Lambda_k^(d) (d u) \
                & -integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^bullet (upright(d) u) \
        &+ macron(Z)_(k,tau) (event(k), status(k), covariate(k), treat(k), history(k-1)) + integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^c ( d u)] \
                &+ integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (upright(d) a)- Psi_tau (P)
$
Now note that 
$
    & integral_(event(k - 1))^tau (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) (N^bullet_k (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(bullet, s, k-1) upright(d) s) \   
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &-Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
        &+ integral_(event(k-1))^(tau and event(k)) (Qbar(k-1)(u))/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
$
Let us calculate the second integral
$
    & Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
    &= Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) (S^c (u | history(k-1)) S (u | history(k-1)))/(S^c (u | history(k-1)) S (u | history(k-1)))^2 hazard(bullet, s, k-1) upright(d) s \
        &= Qbar(k-1)(tau) (1/(S^c (event(k) and tau | history(k-1)) S (event(k) and tau | history(k-1)))-1)
$
where the last line holds by the Duhamel equation (or using that the antiderivative of $- f' / f^2$ is $1/f$).
The first of these integrals is equal to
$
    &integral_(event(k-1))^(tau and event(k)) (Qbar(k+1)(u))/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, u, k-1) upright(d) u \
        &= integral_(event(k-1))^(tau and event(k)) [integral_(0)^(u) S(s | history(k-1)) cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+  integral_(0)^(u) S(s | history(k-1)) cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
            &+  integral_(0)^(u) S(s | history(k-1)) cumhazard(k-1, y, d s)]  \
        &times 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, u, k-1) upright(d) u \
        &= integral_(event(k-1))^(tau and event(k)) integral_(s)^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, u, k-1) upright(d) u [S(s | history(k-1)) cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+ S(s | history(k-1)) cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
            &+  S(s | history(k-1)) cumhazard(k-1, y, d s)]
$
Now note that
$
    & integral_(s)^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, u, k-1) upright(d) u \
        &=  1/(S^c (tau and event(k) | history(k-1)) S (tau and event(k) | history(k-1))) - 1/(S^c (s | history(k-1)) S (s | history(k-1)))
$
Setting this into the previous integral, we get
$
    &-integral_(event(k-1))^(tau and event(k))  1/(S^c (s))   hazard(bullet, u, k-1) upright(d) u [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] \
        &+ 1/(S^c (tau and event(k) | history(k-1)) S (tau and event(k) | history(k-1))) Qbar(k-1) (tau and event(k))
$
Thus, we find
$
    & integral_(event(k - 1))^tau (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) (N^bullet_k (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(bullet, s, k-1) upright(d) s) \   
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &-Qbar(k-1)(tau) integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
        &+ integral_(event(k-1))^(tau and event(k)) (Qbar(k-1)(u))/(S^c (u | history(k-1)) S (u | history(k-1))) hazard(bullet, s, k-1) upright(d) s \
        &=(Qbar(k-1)(tau) - Qbar(k-1)(event(k))) 1/(S^c (event(k) | history(k-1)) S (event(k) | history(k-1))) bb(1){event(k) <= tau} \
        &-(Qbar(k-1)(tau) (1/(S^c (event(k) and tau | history(k-1)) S (event(k) and tau | history(k-1))))-1) \
        &-integral_(event(k-1))^(tau and event(k))  1/(S^c (s))   hazard(bullet, u, k-1) upright(d) u [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] \
        &+ 1/(S^c (tau and event(k) | history(k-1)) S (tau and event(k) | history(k-1))) Qbar(k-1) (tau and event(k)) \
        &=- integral_(event(k-1))^(tau and event(k))  1/(S^c (s))   hazard(bullet, u, k-1) upright(d) u [ cumhazard(k-1, a, d s)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k-1)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ) \
        &+  cumhazard(k-1, ell, d s)  \
        & #h(3cm) times (mean(P) [Qbar(k+1) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) \
        &+  cumhazard(k-1, y, d s)] +Qbar(k-1)(tau) 
$
