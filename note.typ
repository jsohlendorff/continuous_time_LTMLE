#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
///#import "@preview/cetz:0.3.3"
#import "@preview/cheq:0.2.2": checklist

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

= TODO

- [x] Clean up figures.
- [x] Clean up existence of compensator + integral. 
- [x] identifiability. My potential outcome approach. Add figure for potential outcome processes.
      Show full identification formula without reweighting
- [x] Censoring. Independent censoring IPCW rigorously.
- [x] Consistency of estimator. Skip not done in other papers.
- [/] Efficient influence function. Cleanup.
- [ ] Simulation study (ML?).
- [/] Debiased estimator
- [/] DR properties + ML rates/criteria (rate conditions + conditions for $hat(nu)^*$)
- [/] Cross-fitting
- [x] Discussion. Bayesian approach + pooling/rare events. 

= Introduction
In medical research, the estimation of causal effects of treatments over time is often of interest.
We consider a longitudinal continuous-time setting that is very similar to @rytgaardContinuoustimeTargetedMinimum2022
in which patient characteristics can change at subject-specific times. 
This is the typical setting of registry data, which usually
contains precise information about when events occur, e.g.,
information about drug purchase history, hospital visits, and laboratory measurements.
This approach offers an advantage over discretized methods, as it eliminates the need to select a time grid mesh for discretization,
which can affect both the bias and variance of the resulting estimator.
A continuous-time approach would adapt to the events in the data. 
Furthermore, continuous-time data captures more precise information about when events occur, which may be valuable in a predictive sense.
Let $tauend$ be the end of the observation period.
We will focus on the estimation of the interventional cumulative incidence function in the presence of time-varying confounding at a specified time horizon $tau < tauend$.

#assumption("Bounded number of events")[
In the time interval $[0, tauend]$ there are at most $K - 1 < oo$ many changes of treatment and
        covariates in total for a single individual.
        We let $K-1$ be given by the maximum number of non-terminal events for any individual in the data.
] <assumptionbounded>

#assumption("No simultaneous jumps")[
    The counting processes $N^a$, $N^ell$, $N^y$, $N^d$, and $N^c$ have with probability 1 no jump times in common. 
] <assumptionnosimultaneous>

Let $kappa_i (tau)$ be the number of events for individual $i$ up to time $tau$.
In @rytgaardContinuoustimeTargetedMinimum2022, the authors propose a continuous-time LTMLE for the estimation of causal effects in which a single step of the targeting procedure must update each of the nuisance estimators $sum_(i = 1)^n kappa_i (tau)$ times. We propose an estimator where the number of nuisance parameters is reduced to $tilde max_i kappa_i (tau)$ in total,
and, in principle, only one step of the targeting procedure is needed to update all nuisance parameters.
We provide an iterative conditional expectation formula that, like @rytgaardContinuoustimeTargetedMinimum2022,
iteratively updates the nuisance parameters. The key difference is that the estimation of the nuisance parameters can be performed
by going back in the number of events instead of going back in time.
The different approaches are illustrated in @fig:timegridrytgaard and @fig:eventgrid
for an outcome $Y$ of interest. 
Moreover, we argue that the nuisance components can be estimated with existing machine learning algorithms
from the survival analysis and point process literature.
As always let $(Omega, cal(F), P)$ be a probability space on which all processes
and random variables are defined.

#figure(cetz.canvas(length: 1cm, {
  import cetz.draw: *

  set-style(
            mark: (fill: black, scale: 2),
            stroke: (thickness: 1pt, cap: "round"),
            angle: (
                radius: 0.3,
                label-radius: .8,
                fill: green.lighten(80%),
                stroke: (paint: green.darken(50%))
            ),
            content: (padding: 8pt)
        )
  
  let time_grid(cord_start,cord_end, time_values, inc: 0.1, anchor: "north") = {
      // Main axis line
      set-style(mark: (end: ">"))
      line(cord_start, cord_end)
      set-style(mark: none)

      // General time line
      let early_stop = cord_end.first() - 1/10 * cord_end.first()
      let t_grid = frange(cord_start.first()+inc,early_stop - inc, inc)
      
      // Start line
      line((cord_start.first(), -2*inc+cord_start.last()), (cord_start.first(), 2*inc+cord_start.last()), name:"lstart")
      content("lstart.start", [], anchor: "east")
      
      // End line
      line((early_stop - inc, -2*inc+cord_end.last()), (early_stop - inc, 2*inc+cord_end.last()), name: "lend")
      content("lend.start", [#text(size: 12pt)[$tau_"end"$]],anchor: "north")

      // Draw grid
      //for i in t_grid {
      //  line((i, -inc+cord_start.last()), (i, inc+cord_start.last()))    
      //}

      // Deal with the marks/events
      let event_list = ()
      for t in range(0, time_values.len()) {
        event_list.push((name: "v" + str(t), value: time_values.at(t), mformat: $T_( #(t+1) )$))
      }
      for v in event_list {
        line((v.value + cord_start.first(), -2*inc+cord_start.last()), (v.value+cord_start.first(),2*inc+cord_start.last()), name: v.name)
        
        content(v.name + ".start", [#text(size: 12pt)[#v.mformat]], anchor: anchor)
      }
  }
    for v in (2,4) {
        line((v, 0.75), (v, 1.25), stroke: red)
    }
    // Deal with the marks/events
    
    let grid2 = (1,1.7, 2.4,2.8)
    
    group({time_grid((0,1),(5,1), grid2, anchor: "north-east")})
    set-style(mark: (end: ">", scale: 1))
    bezier((1,1.25), (2,1.25),(1.5,2.4), stroke: blue)
    bezier((1.7,0.75), (2,0.75), (1.85,0.25), stroke: blue)
    bezier((2.4,1.25), (4,1.25), (3,2), stroke: blue)
        bezier((2.8,0.75), (4,0.75), (3.4,0.25), stroke: blue)
}), caption:  [The "usual" approach where time is discretized. Each event time and its corresponding mark
    is rolled forward to the next time grid point, that is the values of the observations are updated based on the
    on the events occuring in the previous time interval.
]) <fig:discretetimegrid>

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

// Let $cumhazard(k, x, t)$ be the cumulative hazard of $x$ of the $(k+1)$'th event at time $t$ given the history up to the $k$'th event.
// We focus on estimating $cumhazard(k, x, t)$ for $k = 0, dots, K$ for $K >= 0$ rather than $Lambda^x (t \| cal(F)_(t -))$.
// Here $cal(F)_(T_k)$ is the information up to the $k$'th event -- a so-called stopping time $sigma$-algebra.
//Each of these $sigma$-algebras can be represented by a fixed number of random variables, so that regression can be applied at each event point. 
//We let $pi_0(dot | covariate(0))$ be the density of the baseline treatment given the covariates at time 0
//(with respect to some measure $nu_a$) and
//$mu_0$ be the density of time-varying covariates at time 0 (with respect to some measure $nu_ell$).

= Setting and Notation
First, we assume that at baseline,
we observe the treatment $treat(0)$ and the time-varying confounders
at time 0, $covariate(0)$. The time-varying confounders may principally include covariates
which do not change over time, but for simplicity of notation, we will include them among
those that do change over time.
Throughout, we assume that we have two treatment options, $A(t) = 0, 1$ (e.g., placebo and active treatment),
where $A(t)$ denotes the treatment at time $t$.
The time-varying confounders are assumed to take values in a finite subset $cal(L) subset RR^m$.
//and that $L(t) : Omega -> RR^m$ and $A(t) : Omega -> RR$ are measurable for each $t >= 0$, respectively.
These processes are assumed to be càdlàg, jump processes.
Furthermore, the times at which the treatment and covariates may change 
are dictated entirely by the counting processes $N^a$ and $N^ell$, respectively
in the sense that $Delta A (t) != 0$ only if $Delta N^a (t) != 0$ and $Delta L (t) != 0$ only if $Delta N^ell (t) != 0$.
//The jump times of these counting processes
//thus represent visitation times. 

Since our setup will be a competing risk setup,
we also have counting processes representing
the event of interest and the competing event.
We let $N^y$ and $N^d$ be counting processes corresponding to the primary and competing event, respectively.
//Finally, let $N^c$ be the counting process for the censoring counting process.
We initially assume no censoring, but we will later include it.
We assume that the jump times differ with probability 1 (@assumptionnosimultaneous).
Moreover, we assume that only a bounded number of events occur for each individual in the time interval $[0, tauend]$ (@assumptionbounded).
Thus, we have observations from a the jump process $(N^a (t), A (t), N ^ell (t), L(t), N^y (t), N^d (t))$,
and we let $cal(F)_t = sigma ((N^a (s), A(s), N^ell (s), L(s), N^y (s), N^d (s)) | s <= t)$ be the natural filtration generated by the processes up to time $t$.
//Since the filtration is the natural filtration, it follows that the stopping time
Furthermore, define $sigma$-algebra $history(k) = sigma(event(k), status(k), treat(k), covariate(k)) or history(k-1)$ and
$history(0) = sigma(treat(0), covariate(0))$, representing the information up to the $k$'th event.
Here we tacitly allow the event times after the first event to be $oo$.
We observe $O=history(K) = (event(K), status(K), event(K-1), status(K-1), treat(K-1), covariate(K-1), dots, treat(0), covariate(0)) ~ P in cal(M)$ where
$cal(M)$ is the set of all probability measures. 
We also impose the condition that the last event has to be a terminal event, i.e., $status(K) = y$ or $d$
if $event(K-1) < oo$.
Let $densitytrt(t, k)$ be the probability of being treated at the $k$'th event $history(k-1)$
given that the event time is $t$ and that the $k$'th event is a visitation time
and let $densitytrtmeasure(t, d a, k)$ be the corresponding probability measure.
Let $densitycov(t, dot, k)$ be the probability measure for the covariate value at the $k$'th event given $history(k-1)$
given that the event time is $t$ and that the $k$'th event is a covariate event.
Let $hazard(x, t, k-1)$ be the hazard of the $k$'th event at time $t$ given $history(k-1)$ (@assumptionabscont).
Our overall goal is to estimate the interventional cumulative incidence function at time $tau$,
$
    Psi^g (tau) = mean(P) [tilde(N)^y_tau],
$
where $tilde(N)^y_t$ is the potential outcome representing
the counterfactual outcome $N_t^y = sum_(k=1)^K bb(1) {event(k) <= t, status(k) =y}$ had the treatment
regime (starting and staying on treatment at every visitation time), possibly contrary to fact, been followed.
The necessary conditions for the potential outcome framework are given in @thm:identifiability.
We recognize at this point that visitation times may not actually be that irregular,
but regularly scheduled as they are in a randomized control trial. This will likely _not_ change our results for identification, estimation,
and debiasing. For instance, even if $cumhazard(k, a, t)$ were fully known and deterministic,
the efficient influence function
given in @thm:eif and the iterative conditional expectation formula (@eq:ice2 and @eq:ipcw) are not likely to change
based on the form given in these theorems.

#assumption("Conditional distributions of jumps")[
    We assume that the conditional distributions $P(event(k) in dot | history(k-1)) lt.double m$ $P$-a.s., where $m$ is the Lebesgue measure on $RR_+$.
        ] <assumptionabscont>

//We now take an interventionalist stance to causal inference such as the one given in @ryalenPotentialOutcomes.
From observational data, we will emulate a randomized controlled trial in continuous-time. 
In the continuous-time longitudinal setting, this can e.g., correspond to a trial in which there is perfect compliance
with the treatment protocol.
Our approach is inspired by the conditions of @ryalenPotentialOutcomes, but we do not
apply martingale theory.
Moreover, the identification conditions do not require
the existence of an entire potential outcome process. Instead
the conditions are stated for identification at the time horizon of interest.
While our theory provides a potential outcome framework, it is unclear at this point
how graphical models can be used to reason about the conditions (see @richardson2013single for the discrete time approach).
However, one may define a (stochastic)#footnote[The reason we write stochastic is that the treatment consists of two components; the total compensator for the treatment and mark probabilities. Since these two components are inseparable, the intervention of interest is not a static intervention. ]
intervention with respect to a local independence graph (@roeysland2024) but we do not further pursue this here.
For simplicity, we assume that we are only interested in the effect of staying on treatment ($A(t) = 1$ for all $t > 0$) and starting on treatment ($A(0) = 1$).

We now define the stopping time $T^a$ as the time of the first visitation event where the treatment plan is not followed, i.e.,
$
    T^a = inf_(t >= 0) {A(t) = 0} = inf_(k > 1) {event(k) | status(k) = a, treat(k) != 1} and oo bb(1) {A(0) = 1}
$
where we use that $oo dot 0 = 0$. 

#theorem[
We suppose that there exists a potential outcome $tilde(Y)_tau = tilde(N)_tau^y$ at time $tau$ such that

- *Consistency*: $tilde(Y)_tau bb(1) {T^a > tau} = Y_tau bb(1) {T^a > tau}$.
- *Exchangeability*: We have
   $
       &tilde(Y)_tau bb(1) {event(j) <= tau < event(j+1)}
       perp treat(k) | history(k), event(k), status(k) = a, quad forall j>=k>0, \
       &tilde(Y)_tau bb(1) {event(j) <= tau < event(j+1)}
       perp treat(0) | covariate(0), quad forall j>=0.
   $ <eq:exchangeability>
    - *Positivity*: The measure given by $d R = W d P$ where $W^*_t = product_(k=1)^(N_t) ((bb(1) {treat(k) = 1}) / (densitytrt(event(k), k)))^(bb(1) {status(k) = a}) (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0)))$ is a probability measure,
  where $N_t = sum_(k=1)^(K-1) bb(1) {event(k) <= t}$.

Then the estimand of interest is identifiable by
$
    Psi_(tau)^g (P) = bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t].
$
]<thm:identifiability>
#proof[
    Write $tilde(Y)_t = sum_(k=1)^K bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau$.
    The theorem is shown if we can prove that $mean(P) [bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau] = mean(P) [bb(1) {event(k-1) <= tau < event(k)} Y_tau W_tau]$
    by linearity of expectation.
    We have that for $k >= 1$,
    $
        bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} Y_tau W_tau] &= bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} bb(1) {T^a > tau} Y_tau W_tau] \
            &=bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} bb(1) {T^a > tau} tilde(Y)_tau W_tau] \
            &=bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau W_tau] \
            &=bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau W_(event(k-1)) ]\
            &=bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau ((bb(1) {treat(k-1) = 1}) / (densitytrtprev(treat(k-1), event(k-1), k)))^(bb(1) {status(k-1) =a}) W_(event(k-2)) ]\
            &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau | history(k-2), status(k-1), event(k-1), treat(k-1)] \
                &qquad times ((bb(1) {treat(k-1) = 1}) / (densitytrtprev(treat(k-1), event(k-1), k)))^(bb(1) {status(k-1) =a}) W_(event(k-2)) ]\
                        &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau< event(k)} tilde(Y)_tau | history(k-2), status(k-1), event(k-1)] \
                &qquad times ((bb(1) {treat(k-1) = 1}) / (densitytrtprev(treat(k-1), event(k-1), k)))^(bb(1) {status(k-1) =a}) W_(event(k-2)) ]\
            &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau | history(k-2), status(k-1), event(k-1)] \
                &qquad times mean(P) [((bb(1) {treat(k-1) = 1}) / (densitytrtprev(treat(k-1), event(k-1), k)))^(bb(1) {status(k-1) =a}) | history(k-2), status(k-1), event(k-1)] W_(event(k-2)) ]\
            &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau | history(k-2), status(k-1), event(k-1)] W_(event(k-2)) ]\
            &=bb(E)_P [ bb(E)_P [ bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau | history(k-3), status(k-2), event(k-2), treat(k-2)] W_(event(k-2)) ]\
    $
    Iteratively applying the same argument, we get that
    $bb(E)_P [  bb(1) {event(k-1) <= tau < event(k)} tilde(Y)_tau ] = bb(E)_P [  bb(1) {event(k-1) <= tau < event(k)} Y_tau W_tau]$ as needed.
]
By the intersection property of conditional independence, we see that a sufficient condition for the first exchangeability condition in @eq:exchangeability
is that
$
    tilde(Y)_tau
    perp treat(k) | event(j) <= tau < event(j+1), history(k), event(k), status(k) = a, quad forall j>=k>0, \
    bb(1) {event(j) <= tau < event(j+1)}
    perp treat(k) | tilde(Y)_tau, history(k), event(k), status(k) = a, quad forall j>=k>0. \
$
An illustration of the consistency condition is given in @fig:potentialoutcome.

The second condition may in particular be too strict in practice as the future event times
may be affected by prior treatment.
Alternatively, it is possible to posit the existence of a potential outcome for each event separately and
get the same conclusion. The overall exchangeability condition may be stated differently, but the consistency condition is very similar. 
Specifically, let $tilde(Y)_(tau, k)$ be the potential outcome at event $k$
corresponding to $bb(1) {event(k) <= tau, status(k) =y}$.
Then the exchangeability condition is that $tilde(Y)_(tau, k) perp treat(j) | history(j-1), event(j), status(j) = a)$ for $0 <= j < k$ and $k = 1, dots, K$.
However,
it has been noted #citep(<RobinsLongitudinal2001>) in discrete time that the existence of multiple potential outcomes
can be restrictive and that the resulting exchangeability condition may be too strong. 

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
    The left panel shows the potential outcome process $tilde(Y)_t$ (dashed) and the observed process $Y_t$ (solid).
    The right panel shows the treatment process $A(t)$. At time $T^a$, the treatment is stopped and the processes
    may from then on diverge. 
]) <fig:potentialoutcome>

We are now ready to give an iterated conditional expectations formula for the target parameter in the case with no censoring.
The algorithm can be foundin @thm:parameter, but we will state more explicitly in the
next section how to allow for censoring.
Note that the iterative conditional expectations formula in terms of the event-specific cause-specific hazards
and the density for the time-varying covariates (@thm:hazardrepresentation) actually shows
that our target parameter is the same as the one given in @rytgaardContinuoustimeTargetedMinimum2022
with no competing event (*TODO*: show this more explicitly) under the stated identifiability conditions.

//First, and foremost though, we will remark
//that this can be used to write down the target parameter directly in terms of the event-specific cause-specific hazards
//and the density for the covariate process. 

// should just be identification not of conditional densities
#theorem[
    Let $W_(k, j) = W_(event(j)) / W_(event(k))$ for $k < j$ (defining $0/0 = 0$).
    Let $macron(Q)_K = bb(1) {event(K) <= tau, status(K) = y}$ and
    $macron(Q)_k = mean(P) [sum_(j=k+1)^K  W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | history(k)]$.
    Then,
    $
            macron(Q)_(k-1)&= mean(P) [bb(1) {event(k) <= tau, status(k) = ell) macron(Q)_(k)(treat(k-1), covariate(k), event(k), status(k), history(k-1)) \
                &+ bb(1) {event(k) <= tau, status(k) = a) macron(Q)_(k)(1, covariate(k-1), event(k), status(k), history(k-1)) \
            & + bb(1) {event(k) <= tau, status(k) = y) mid(|) history(k-1)]
    $
    for $k = K, dots, 1$.
    Thus, $Psi^g_tau (P) = mean(P) [sum_(k=1)^K W_(event(k-1)) bb(1) {event(k) <= tau, status(k) = y)]= mean(P) [macron(Q)_0 W_0] = mean(P) [ mean(P) [macron(Q)_0 | treat(0) = 1, covariate(0)] ]$.
]<thm:parameter>

#proof[
    //First note that the $macron(Q)_k$ only need to be evaluated when the person is at risk. 
    First, we find
    $
        macron(Q)_k &= mean(P) [sum_(j=k+1)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | history(k)] \
            &= mean(P) [mean(P) [mean(P) [sum_(j=k+1)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y}  | history(k+1)]  | event(k+1), status(k+1), history(k) ] | history(k)] \
            &= mean(P) [bb(1) {event(k+1) <= tau, status(k+1) = y} W_(k,k+1) \
                &#h(2cm)+ mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)]
                mid(|) history(k)] \
            &= mean(P) [bb(1) {event(k+1) <= tau, status(k+1) = y} W_(k,k+1) \
                &#h(2cm)+ bb(1) {event(k+1) <= tau, status(k+1) = a}  mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)] \
                &#h(2cm)+ bb(1) {event(k+1) <= tau, status(k+1) = ell}  mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)]
                mid(|) history(k)] \
             &= mean(P) [bb(1) {event(k+1) <= tau, status(k+1) = y} \
                &#h(2cm)+ bb(1) {event(k+1) <= tau, status(k+1) = a}  mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)] \
                &#h(2cm)+ bb(1) {event(k+1) <= tau, status(k+1) = ell}  mean(P) [mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)]
                mid(|) history(k)] \
                         &= mean(P) [bb(1) {event(k+1) <= tau, status(k+1) = y} \
                &#h(2cm)+ bb(1) {event(k+1) <= tau, status(k+1) = a}  mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | event(k+1), status(k+1), history(k)] \
                &#h(2cm)+ bb(1) {event(k+1) <= tau, status(k+1) = ell}  mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | history(k+1)]  | history(k)] 
    $
    by the law of iterated expectations and that
    $
        (event(k) <= tau, status(k) = y) subset.eq (event(j) <= tau, status(j) in {a, ell})
    $
    for all $j = 1, dots, k-1$ and $k = 1, dots, K$. The second statement simply follows from the fact that
    $
        &mean(P) [W_(k-1,k) macron(Q)_(k)(treat(k), covariate(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = a, history(k-1)] \
            &= mean(P) [(bb(1) {treat(k) = 1})/(densitytrt(event(k), k))  macron(Q)_(k)(1, covariate(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = a, history(k-1)] \
            &= mean(P) [(densitytrt(event(k), k))/(densitytrt(event(k), k))  macron(Q)_(k)(1, covariate(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = a, history(k-1)] \
            &=macron(Q)_(k)(1, covariate(k-1), event(k), status(k), history(k-1))
    $
    by the law of iterated expectations. 
] 

#theorem[
    Let $ Qbarmiss(k)(Q)$ be defined as $Qbar(k)$ in @thm:parameter (*TODO*: use one notation).
    Denote by $S_k (s- | history(k-1)) = prodint2(s, event(k-1), t) (1 - sum_(x = ell, a, d, y) hazard(x, s, k-1) d s)$
    the left limit of the survival function of the $k$'th event at time $s$ given $history(k-1)$.
    Then, we have
    $
        & p_(k a) (t | history(k-1)) = integral_(history(k-1))^t S_k (s- | history(k-1)) Qbar(k+1) (1, covariate(k-1), s, a, history(k-1)) hazard(a, s, k) d s \
            &p_(k ell) (t | history(k-1)) \
            &= integral_(history(k-1))^t S_k (s- | history(k-1)) (mean(P) [Qbar(k+1) (treat(k-1), covariate(k), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)] ) hazard(y, s, k) d s \
            & p_(k y) (t | history(k-1)) = integral_(history(k-1))^t S_k (s- | history(k-1))  hazard(y, s, k) d s,
    $
    and we can identify $Qbar(k)$ via the intensities as
#math.equation(block: true, numbering: "(1)")[$
    Qbar(k) &= p_(k a) (tau | history(k-1)) + p_(k ell) (tau | history(k-1)) + p_(k y) (tau | history(k-1)).
$] <eq:cuminc>] <thm:hazardrepresentation>
#proof[
    To prove the theorem, we simply have to find the conditional density of $(event(k), status(k))$ given $history(k-1)$.
    First note that we can write,
    $
        macron(Q)_(k-1)&= mean(P) [bb(1) {event(k) <= tau, status(k) = ell) mean(P) [macron(Q)_(k)(treat(k-1), covariate(k), event(k), status(k), history(k-1)) | event(k), status(k) = ell, history(k-1)] \
                &+ bb(1) {event(k) <= tau, status(k) = a) macron(Q)_(k)(1, covariate(k-1), event(k), status(k), history(k-1)) \
            & + bb(1) {event(k) <= tau, status(k) = y) mid(|) history(k-1)]
    $ <eq:macronQ>
    Since $hazard(x, t, k-1)$ is the cause-specific hazard of the $k$'th event at time $t$ given $history(k-1)$ and that the event was of type $x$, it follows that
    the conditional density of $(event(k), status(k))$ given $history(k-1)$ is given by
    $
        p (t, d | history(k-1) = f_(k-1)) = prodint2(s, event(k-1), t) (1 - sum_(x = ell, a, d, y) hazard(x, s, k-1) d s) hazard(x, t, k-1).
    $
    Putting this into the expectation of @eq:macronQ, we get the claim. 
]

= Censoring
In this section, we introduce a right-censoring time $C>0$
at which we stop observing the multivariate jump process
$Z(t) = (N^a (t), A (t), N ^ell (t), L(t), N^y (t), N^d (t))$.
Denote by $N^c (t) = bb(1) {C <= t}$ the counting process for the censoring process
and its filtration $cal(G)_t = sigma(N^c (s) | s <= t)$.
Let $T^e$ further denote the terminal event time, $T^e = inf_(t>0) {N^y (t) + N^d (t) = 1}$.
Then we can view the censoring as being coarsened by the terminal event time
$T^e$. The full data filtration is therefore given by
$
    cal(F)^"full"_t = cal(F)_t or cal(G)_t
$
Let $hazardprev(c, t, k)$ be the cause-specific hazard of the $k$'th event at time $t$ given the full history and that the event was a censoring event
and define correspondingly $S^c (t- | history(k-1)) = prodint2(s, event(k-1), t) (1 - hazard(c, s, k-1) d s)$ the censoring survival function. 
Unfortunately, we only ever fully observe the process $t mapsto (Z(t and C), N^c (t and T^e))$
which is adapted and predictable with respect to the filtration $cal(F)^"full"_(t and C and T^e) subset.eq cal(F)^"full"_t$.
From this, we get the observed data,
$
    macron(T)_k &= C and event(k) \
    macron(D)_k &= cases(status(k) "if" C > event(k), "c" "otherwise") \
    A(macron(T)_k) &= cases(treat(k) "if" C > event(k), treat(k-1) "otherwise") \
    L(macron(T)_k) &= cases(covariate(k) "if" C > event(k), covariate(k-1) "otherwise")
$
Denote by
    $
        N^(r,a) (d t, d a) &= sum_(k=1)^K delta_(status(k)) (a) delta_((event(k), treat(k))) (d t, d a) \
        N^(r,ell) (d t, d ell) &= sum_(k=1)^K delta_(status(k)) (ell) delta_((event(k), covariate(k))) (d t, d ell) \
        N^(r,y) (d t) &= sum_(k=1)^K delta_(status(k)) (y) delta_(event(k)) (d t) \
        N^(r,d) (d t) &= sum_(k=1)^K delta_(status(k)) (d) delta_(event(k)) (d t) \
        N^(r,c) (d t) &= sum_(k=1)^K delta_(status(k)) (c) delta_(event(k)) (d t)
    $
the corresponding random measures of the fully observed $Z(t)$ and $N^c (t)$.
We provide the necessary conditions in terms of independent censoring
(or local independence conditions) in the sense of @andersenStatisticalModelsBased1993.
It follows from arguments given in @thm:jointdensity
that the filtration generated by the random measures is necessarily
the same as $cal(F)^"full"_t$. We are now ready to state the main theorem
which allows us to prove that the ICE IPCW estimator is valid.
A simple implementation of the IPCW is provided in @alg:ipcwice.

#theorem[
    Assume that the intensity processes of $N^(r,x), x= a,ell,d,y$ with respect to the filtration
    $cal(F)_t$ are also the intensities with respect to the filtration
    $cal(F)^"full"_t$. Additionally, assume also that the intensity process of $N^c (t)$ with respect to the filtration
    $cal(G)_t$ is also the intensity process with respect to the filtration
    $cal(F)^"full"_t$.
    Then the cause-specific hazard measure $tilde(Lambda)^x_k$ for the $k$'th jump of $t mapsto (Z(t and C), N^c (t and T^e))$ at time $t$ given $history(k-1)$
    is given by
    $
        tilde(Lambda)^x_k (d t | history(k-1)) &= hazard(x, t, k-1) d t, qquad x = a, ell, d, y, c \
        tilde(pi)_k (a, t, history(k-1)) &= densitytrt(t, k) \
        tilde(mu)_k (l, t, history(k-1)) &= densitycov(l, t, k) \
    $
    Consequently, we have that
    #math.equation(block: true, numbering: "(1)")[$
        Qbar(k-1) &= mean(P) [(bb(1) {eventcensored(k) <= tau, statuscensored(k) = ell})/( S_k^c (eventcensored(k-1) - | historycensored(k-1)) ) Qbar(k)(treatcensored(k-1), covariatecensored(k), eventcensored(k), statuscensored(k), historycensored(k-1)) \
            &#h(1.5cm) + (bb(1) {eventcensored(k) <= tau, statuscensored(k) = a}) /(S_k^c (eventcensored(k-1) - | historycensored(k-1)))  Qbar(k) (1, covariatecensored(k-1), eventcensored(k), statuscensored(k), historycensored(k-1)) \
            &#h(1.5cm) + (bb(1) {eventcensored(k) <= tau, statuscensored(k) = y}) /(S_k^c (eventcensored(k-1) - | historycensored(k-1))) mid(|) historycensored(k-1)]
    $] <eq:ipcw>
    for $k = K-1, dots, 1$. 
    Then, 
    $
        Psi_tau lr((Q)) = mean(P) [  Qbar(0) (1, covariate(0))].
    $<eq:ice2>
] <thm:ice>
#proof[
    // positivity?
    The last statement (@eq:ipcw and @eq:ice2) follows from the first statement and @thm:hazardrepresentation.
    The compensator of the random measures $N^(r,x)$ with respect to the filtration $cal(F)_t$ is given by
    $
        Lambda^(r,a) (dif t, dif a) = sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} densitytrtmeasure(t, dif a, k) hazard(y, t, k) dif t\
        Lambda^(r, ell) (dif t, dif ell) = sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)}   densitycov(t, dif ell, k) hazard(ell, t, k) dif t \
        Lambda^(r, y) (dif t) = sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)}  hazard(y, t, k) dif t\
        Lambda^(r, d) (dif t) = sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)}  hazard(d, t, k) dif t
    $
    by @thm:jointdensity and by assumption is also the compensator for the filtration $cal(F)^"full"_t$. By the innovation theorem (Section II.4.2 of @andersenStatisticalModelsBased1993),
    $
        tilde(Lambda)^(r,a) (d t, d a) = sum_(k=1)^K bb(1) {event(k-1) and C < t <= event(k) and C}  hazard(a, t, k-1) densitytrt(t, k-1) d t \
        tilde(Lambda)^(r, ell) (d t, d ell) = sum_(k=1)^K bb(1) {event(k-1) and C < t <= event(k) and C} hazard(ell, t, k-1) densitycov(t, d ell, k-1) d t \
        tilde(Lambda)^(r, y) (d t) = sum_(k=1)^K bb(1) {event(k-1) and C < t <= event(k) and C} hazard(y, t, k-1) d t\
        tilde(Lambda)^(r, d) (d t) = sum_(k=1)^K bb(1) {event(k-1) and C < t <= event(k) and C} hazard(d, t, k-1) d t
    $
    is the compensator of the random measures $N^(r,x)$ with respect to the filtration $cal(F)^"obs"_t$.
    This can be seen by noting that $cal(F)^"obs"_t subset.eq cal(F)^"full"_t$ and
    that the censoring function $C(t) = bb(1) {t <= C}$ is adapted to the filtration $cal(F)^"full"_t$.
    On the other hand, we can apply @thm:jointdensity directly to the observed process to get that
    $
        tilde(Lambda)^(r,a) (d t, d a) = sum_(k=1)^K bb(1) {eventcensored(k-1) < t <= eventcensored(k)} tilde(pi)_k (a, t, historycensored(k-1))  tilde(Lambda)^x_k (d t | historycensored(k-1)) \
        tilde(Lambda)^(r, ell) (d t, d ell) = sum_(k=1)^K bb(1) {eventcensored(k-1) < t <= eventcensored(k)} tilde(mu)_k (l, t, historycensored(k-1))  tilde(Lambda)^x_k (d t | historycensored(k-1)) \
        tilde(Lambda)^(r, y) (d t) = sum_(k=1)^K bb(1) {eventcensored(k-1) < t <= eventcensored(k)}  tilde(Lambda)^x_k (d t | historycensored(k-1)) \
        tilde(Lambda)^(r, d) (d t) = sum_(k=1)^K bb(1) {eventcensored(k-1) < t <= eventcensored(k) }  tilde(Lambda)^x_k (d t | historycensored(k-1)) \
    $ <eq:lambda>
    where $tilde(Lambda)^x_k (d t | historycensored(k-1))$ is cause-specific cumulative hazard of the $k$'th event at time $t$ given $historycensored(k-1)$,
    and $tilde(pi)_k (a, t, historycensored(k-1))$ is the density of the treatment process at time $t$ given $historycensored(k-1)$,
        and $tilde(mu)_k (l, t, historycensored(k-1))$ is the density of the covariate process at time $t$ given $historycensored(k-1)$.
    Since the canonical compensator given in @eq:lambda (Theorem 4.3.9 in @last1995marked) determines uniquely the distribution of the marks and the event times,
    the theorem follows. 
    //Alternatively, 
    //looking at the first equation, we get e.g.,
    //$
    //    tilde(pi)_k (a, t, historycensored(k-1))  tilde(Lambda)^x_k (d t | historycensored(k-1)) bb(1) {event(k-1) and C < t <= event(k) and C}  = bb(1) {event(k-1) and C < t <= event(k) and C} hazard(a, t, k-1) densitytrt(t, d a, k-1) d t
    //$
    //Take the expectations on both sides given $history(k-1)$. This probability is by positivity non-zero (?), and therefore
    //    $
    //        tilde(pi)_k (a, t, historycensored(k-1))  tilde(Lambda)^x_k (d t | historycensored(k-1)) = hazard(a, t, k-1) densitytrt(t, d a, k-1)
    //    $
    //Similar derivations now hold for $x= ell, y, d, c$.
]

//The other representations of the target parameter in terms of the intensities are useful directly,
//but we may, as in the discrete, estimate the target parameter by Monte Carlo integration (i.e., direct simulation from the estimated intensities/densities).

In the next section, we will now write $event(k), status(k), treat(k), covariate(k)$ instead of $eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k)$
and $history(k)$ instead of $historycensored(k)$. *NOTE*: Change this. 

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
   
// // #algorithm({
// //   import algorithmic: *
// //     Function("Iterative conditional expectation approach (Method 2)", {
// //     For(cond: $k = K_tau, dots, 1$, {
// //         Assign($cal(R)_(k, tau)$, ${i in {1, dots, n} | D_((k-1),i) in {a, ell}, T_((k-1), i) <= tau}$)
// //         Cmt[Obtain $hat(A)_(i,k)^x (f_j)$ for all pairs $i, j in cal(R)_(k, tau)$, $x in {a, ell, y, d}$ by regressing $(S_((k)), D_((k)) = x)$ on $history(k-1)$]
// //         If(cond: $k < K_tau$, {
// //             Cmt[Obtain from $tilde(Q)_(k)$ predictions for each $i in cal(R)_(k, tau) inter {i | D_((k),i) = ell}$. Regress these on $event(k), status(k) = ell, history(k-1)$ to get $hat(mu) (event(k), history(k-1))$, an estimator of $bb(E)_P [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k), status(k) = ell, history(k-1)]$. ]
// //         })
// //         For(cond: $j in cal(R)_(k, tau)$, {
// //             Assign($hat(p)_(k y) (tau | cal(F)^j_(T_(k-1)))$, $sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (cal(F)^j_(T_(k-1)))) (hat(A)_(i,k)^y (cal(F)^j_(T_(k-1))) - hat(A)_(i-1,k)^y (cal(F)^j_(T_(k-1))))$)
// //             Assign($hat(p)_(k a) (tau | cal(F)^j_(T_(k-1)))$, $bb(1) {k < K_tau} sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (cal(F)^j_(T_(k-1)))) tilde(Q)_(k) (A_k := 1, L^i_k, D^i_k, S_(k,i,j)+ T^i_((k-1)), cal(F)^j_(T_(k-1))) (hat(A)_(i,k)^a (cal(F)^i_(T_(k-1))) - hat(A)_(i-1,k)^a (cal(F)^i_(T_(k-1))))$)
// //             Assign($hat(p)_(k ell) (tau | cal(F)^j_(T_(k-1)))$, $bb(1) {k < K_tau} sum_(i=1)^(c_k (tau)) exp(- sum_(x = a, ell, y, d) hat(A)_(i,k)^x (cal(F)^j_(T_(k-1))))  hat(mu) (S_(k,i,j)+ T^i_((k-1)), cal(F)^j_(T_(k-1))) (hat(A)_(i,k)^ell (cal(F)^i_(T_(k-1))) - hat(A)_(i-1,k)^ell (cal(F)^i_(T_(k-1))))$)
// //             Assign($hat(p) (tau | cal(F)^j_(T_(k-1)))$, $hat(p)_(k a) (tau | cal(F)^j_(T_(k-1))) + hat(p)_(k ell) (tau | cal(F)^j_(T_(k-1))) + hat(p)_(k y) (tau | cal(F)^j_(T_(k-1)))$)
// //         })
// //         Cmt[Regress the predicted values $hat(p) (tau | cal(F)^j_(T_(k-1)))$ on $history(k-1)$ to get $tilde(Q)_(k-1)$; the surrogate model for $Qbar(k-1)$]
// //       })
// //     })
// //     Cmt[From $tilde(Q)_0$ obtain predictions for each $i = 1, dots, n$ and regress on $A_0, L_0$; thereby obtaining $1/n sum_(i=1)^n hat(bb(E)_P) [Qbar(0) (A_0, L_0) | A_0 = 1, L^i_0]$ as an estimator of $Psi_tau lr((Q))$]
// //     // Apply baseline regression    
// //     Return[*null*]
// //   })
// // })
         

//*Note*: The $Qbar(k)$ have the interpretation of the
//heterogenous causal effect after $k$ events.

It is recommended to use @eq:ipcw for estimating $Qbar(k)$ instead of direct computation @eq:cuminc:
The resulting integral representing the target parameter would, in realistic settings, be incredibly highly dimensional.
Specialized approaches may yet exist (see the discussion).
//For estimators of
//the hazard that are piecewise constant, we would need to compute
//ntegrals for each unique pair of history and event times occurring
//in the sample at each event $k$, but see our discussion for an overview of
//approaches which can estimate  @eq:cuminc directly.
//On the other hand, the IPCW approach is very
//sensitive to the specification of the censoring distribution. 

Let $|| dot ||_(L^2 (P)) $ denote the $L^2 (P)$-norm,
that is
$
    || f ||_(L^2 (P)) &= sqrt(mean(P) [f^2 (X)]) = sqrt(integral f^2 (x) P(d x)).
$
Based on this definition, we can give a simple condition for the IPCW ICE estimator to be consistent
in the $L^2 (P)$-norm.

#lemma[
    Define $P_k = P |_(history(k))$ the restriction of $P$ to the $sigma$-algebra generated by the history of the first $k$ events,
    and $P'_(k) = P |_(history(k))$ the restriction of $P$ to the $sigma(event(k), status(k)) or history(k-1)$.
    Assume that $|| hat(nu)_(k+1) - Qbar(k+1) ||_(L^2 ( P_(k+1) )) = o_P (1)$,  $|| hat(Lambda)_(k+1)^c - Lambda_(k+1)^c ||_(L^2 (P'_(k+1))) = o_P (1)$.
    For the censoring, we need that $hat(Lambda)^c_k$ and $Lambda^c_k$ are
    uniformly bounded, that is $hat(Lambda)^c_k (t | f_(k-1)) <= C$ and $Lambda^c_k (t | f_(k-1))<= C$ on the
    interval for all $t in [0, tau]$ for some constant $C>0$ and for $P$-almost all $f_(k-1)$.
    Let $hat(P)_(k)$ denote the regression estimator of step 2 of the algorithm and assume that
    $
        || hat(P)_(k) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] ||_(L^2 (P_k)) = o_P (1)
    $
    where $macron(Z)^a_(k,tau)$ is defined as the integrand of @eq:ipcw.
    Then,
    $
        || hat(nu)_(k) - Qbar(k) ||_(L^2 (P_k)) = o_P (1)
    $ 
]
#proof[
    By the triangle inequality,
    $
        || hat(nu)_(k) - Qbar(k) ||_(L^2 (P_k)) &<= || hat(P)_(k) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] ||_(L^2 (P_k)) \
            &+ || mean(P) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (S^c, hat(nu)_(k+1)) | history(k) = dot] ||_(L^2 (P_k)) \
            &+ || mean(P) [macron(Z)^a_(k,tau) (S^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (S^c, Qbar(k+1)) | history(k) = dot] ||_(L^2 (P_k)) 
    $
    The first term is $o_P (1)$ by assumption. The third term is $o_P (1)$ by Jensen's inequality and by assumption. That the second term is $o_P (1)$ follows from the fact again
    applying Jensen's inequality to see that 
    $
        &|| mean(P) [macron(Z)^a_(k,tau) (hat(S)^c, hat(nu)_(k+1)) | history(k) = dot] - mean(P) [macron(Z)^a_(k,tau) (S^c, hat(nu)_(k+1)) | history(k) = dot] ||_(L^2 (P_k)) \
            &<= sqrt( integral (1/(S^c (t_(k+1) - | f_k)) - 1/(hat(S)^c (t_(k+1) - | f_(k))))^2 bb(1) {t_(k+1) <= tau, d_(k+1) in {a, ell}} hat(nu)_(k+1 )^2 (f_(k+1)) P_(k+1) (dif f_(k+1))) \
            &<= sqrt( integral (1/(S^c (t_(k+1) - | f_k)) - 1/(hat(S)^c (t_(k+1) - | f_(k))))^2 bb(1) {t_(k+1) <= tau} P_(k+1) (dif f_(k+1))) \
            &<= K sqrt( integral (hat(Lambda)^c_(k+1) (t_(k+1) | f_k) - Lambda^c_(k+1) (t_(k+1) | f_k))^2 bb(1) {t_(k+1) <= tau} P_(k+1) (dif f_(k+1)))
    $ <eq:macron2>
    This shows that the second term is $o_P (1)$. In the last equality, we used that the function $x mapsto exp(-x)$ is Lipschitz continuous (since we assume that the hazards are uniformly bounded)
    on the set of possible values for the estimated cumulative hazard and the cumulative hazard. 
]


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

#theorem("Efficient influence function")[
    The efficient influence function is given by
    #text(size: 7.5pt)[$
            phi^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) product_(j = 1)^(k-1) ((bb(1) {treat(j) = 1}) / (densitytrt(event(j), j)))^(bb(1) {status(j) = a}) 1/( product_(j=1)^(k-1) S^c (event(j)- | history(j-1))) bb(1) {status(k-1) in {ell, a}, event(k-1) < tau}  \
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
        &+((pi_(k-1,0) (event(k), history(k-1)))/ (pi_(k-1) (event(k), history(k-1))))^(bb(1) {status(k) = a})integral_(event(k - 1))^(tau) ((S_0^c (u | history(k-1))) / (S^c (u | history(k-1)))-1) (nu^*_(k-1, tau) (d u |history(k-1)) - Qbar(k-1) (d u | history(k-1))) \
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
        &+integral_(event(k - 1))^(tau) ((S_0^c (u | history(k-1))) / (S^c (u | history(k-1)))-1) (nu^*_(k-1, tau) (d u |history(k-1)))
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

== Finite dimensional distributions and compensators

    Let $(tilde(X)(t))_(t >= 0)$ be a $d$-dimensional cadlag jump process,
    where each component $i$ is two-dimensional such that $tilde(X)_i (t) = (N_i (t), X_i (t))$
    and $N_i (t)$ is the counting process for the measurements of
    the $i$'th component $X_i (t)$ such that $Delta X_i (t) != 0$ only if $Delta N_i (t) != 0$
    and $X (t) in cal(X)$ for some Euclidean space $cal(X) subset.eq RR^m$.
    Assume that the counting processes $N_i$ with probability 1 have no simultaneous jumps.
Assume that the number of event times are bounded by a finite constant $K$.
    Furthermore, let $cal(F)_t = sigma(tilde(X)(s) | s <= t) or sigma(W)$ be the natural filtration.
    For each component $tilde(X)_i$, let the corresponding random measure be given by
    $
        N_i (d t, d x) = sum_(k : event(k) < oo) delta_((event(k), X(event(k)))) (d t, d x).
    $
    Let $cal(F)_(T_((k)))$ be the stopping time $sigma$-algebra associated with
the $k$'th event time of the process $tilde(X)$. Furthermore, let $status(k) = j$ if $Delta N_j (event(k)) != 0$ and let $bb(F)_k = cal(W) times (RR_+ times {1, dots, d} times cal(X))^k$.


#theorem("Finite-dimensional distributions")[
    Under the stated conditions of this section, we have
    1.  We have $history(k) = sigma( event(k), status(k), X(event(k))) or history(k-1)$
       and $history(0) = sigma(W)$. 
    2. There exist stochastic kernels $Lambda_(k, i)$ from $bb(F)_k$ to $RR$ and $zeta_(k,i)$ from $bb(F)_k times RR_+$ to $RR_+$ such that the compensator for $N_i$ is given by,
       $
           Lambda_i (d t, d x) = sum_(k : event(k) < oo) bb(1) {event(k-1) < t <= event(k)} zeta_(k,i) (d x, t, history(k-1)) Lambda_(k,i) (d t, history(k-1)). 
       $
       Here $Lambda_(k, i)$ is the cause-specific hazard measure for $k$'th event and the $i$'th component jumping
       and $zeta_(k,i)$ is the conditional distribution of $X_i (event(k))$ given $history(k-1)$ and $event(k)$.
    3. The distribution of $history(n)$ is given by
       $
          &F_n (d w, d t_1, d delta_1, d x_(11), dots, d x_(1 d), dots, d t_n, d delta_n, d x_(n 1), dots, d x_(n d)) \
            &= (product_(i=1)^n bb(1) {t_(i-1) < t_i} prodint2(u, t_(i-1), t_i) (1-sum_(j=1)^d Lambda_(i,j) (d u, f_(i-1))) sum_(j=1)^d delta_j (d delta_i) zeta_(i,j) (d x_(i j), t_i, f_(i-1)) Lambda_(i,j) (d t_i, f_(i-1))) mu (d w),
       $
       and $f_k = (t_k, d_k, x_k, dots t_1, d_1, x_1, w) in bb(F)_k$ for $n in NN$.
       Here $#scale(160%)[$pi$]$ denotes the product integral #citep(<gill1990survey>). 
] <thm:jointdensity>
#proof[
    To prove 1, we first note that since the number of events are bounded,
    we the _minimality_ condition of Theorem 2.5.10 of @last1995marked,
    the filtration $cal(F)^N_t = sigma(N ((0, s], dot) | s <= t) or sigma(W) = cal(F)_t$ where
    $
        N (d t, d x) = sum_(k : event(k) < oo) delta_((event(k), tilde(X)(event(k)))) (d t, d x)
    $
    Thus $history(k) = sigma (event(k), tilde(X)(event(k))) or history(k-1)$
    and $history(0) = sigma(W)$ in view of (2.2.44) of @last1995marked.
    To get 1, simply note that since the counting proceses do not jump at the same time,
    there is a one-to-one corresponding between $status(k)$ and $N^i (event(k))$ for $i = 1, dots, d$.

    To prove 2, simply use Theorem 4.1.11 of @last1995marked which states that
    $
        Lambda(d t, d x) &= sum_(k: event(k) < oo) bb(1) {event(k-1) < t <= event(k)} P( (event(k), tilde(X) (event(k))) in (d t, d x) | history(k-1)) / P(event(k) >= t | history(k-1))  
    $
    is a $P$-$cal(F)_t$ martingale.
    We can write that
    $
        P( (event(k), tilde(X) (event(k))) in (d t, d x) | history(k-1)) / P(event(k) >= t | history(k-1)) &= P(tilde(X) (event(k)) in d x | history(k-1), event(k) = t) P(event(k) in d t | history(k-1)) / P(event(k) >= t | history(k-1))\
    $
    Now write $d x = (d m, d x_1, dots, d x_d)$, so we can write by the no simultaneous jumps condition,
    $
        & P(tilde(X) (event(k)) in d x | history(k-1), event(k) = t) \
            &= sum_(j=1)^d delta_j (d m) P(status(k) = j| history(k-1), event(k) = t) P (X_j (event(k)) in d x_j | history(k-1), event(k) = t, status(k) = j) product_(l != j) delta_((X_l (event(k-1)))) (d x_l)
    $
    Now note that
    $
        N_i (d t, d x) = N (d t, cal(X)_1, {0}, dots, cal(X)_i, {1}, dots , cal(X)_d, {0}) \
    $
    so we find the compensator of $N_i$ to be
    $
        Lambda_i (d t, d x) = sum_k bb(1) {event(k-1) < t <= event(k)} P(status(k) = i| history(k-1), event(k) = t) P (X_i (event(k)) in d x | history(k-1), event(k) = t, status(k) = i) P(event(k) in d t | history(k-1)) / P(event(k) >= t | history(k-1))
    $
    Letting
    $
        zeta_(k,j) (d x, t, f_(k-1)) := P (X_j (event(k)) in d x | history(k-1) = f_(k-1), event(k) = t, status(k) = j) \
        Lambda_(k, j) (d t, f_(k-1)) := P(status(k) = j| history(k-1) = f_(k-1), event(k) = t) P(event(k) in d t | history(k-1) = f_(k-1)) / P(event(k) >= t | history(k-1) = f_(k-1))
    $
    completes the proof of 2.

    3. is simply a straightforward extension of Proposition 1/Theorem 3 of @ryalenPotentialOutcomes
    or an application of Theorem 8.1.2 of @last1995marked. It also follows from iterative applications of 2. 
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
