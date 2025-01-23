#import "@preview/fletcher:0.5.1": node, edge, diagram
// #import "template.typ": conf
#import "template/definitions.typ": *
#import "template/lapreprint.typ": template
#import "@preview/cetz:0.3.1"
#set cite(form: "prose")
#show: template.with(
    title: "A Novel Approach to the Estimation of Causal Effects of Multiple Event Point Interventions in Continuous Time",
    subtitle: "",
    short-title: "Novel Approach to Continuous Time Causal Inference",
    // This is relative to the template file
    // When importing normally, you should be able to use it relative to this file.
    logo: none,
    // You can make all dates optional, however, `date` is by default `datetime.today()`
    theme: red.darken(50%),
    authors: (
        (
            name: "Johan Sebastian Ohlendorff",
            //orcid: "0009-0006-8794-6641",
            email: "johan.ohlendorff@sund.ku.dk",
            affiliations: "1"
        ),
        (
            name: "Anders Munch",
            //orcid: "?",
            email: "a.munch@sund.ku.dk",
            affiliations: "1"
        ),    
        (
            name: "Thomas Alexander Gerds",
            //orcid: "0000-0002-5955-816X",
            email: "tag@sund.ku.dk",
            affiliations: "1"
        )
    ),
    affiliations: (
        (id: "1", name: "University of Copenhagen, Section of Biostatistics"),
    ),
    abstract: (
        (title: "Abstract", content: [In medical research, causal effects of treatments that may change over
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
            processes, enabling robust continuous-time causal effect estimation.]),
    ),
    open-access: false,
    font-face: "New Computer Modern",
)

#show: thmrules.with(qed-symbol: $square$)

// typst-ts-watch

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
        Without loss of register data applications, we assume that the
        maximum number of treatment and covariate changes of an individual
    is bounded by $K = 10,000$. Practically, we shall adapt $K$ to our data and our target parameter.
    We let $K-1$ be given by the maximum number of non-terminal events for any individual in the data.
] <assumptionbounded>

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

#figure(cetz.canvas(length: 0.9cm, {
  import cetz.draw: *

  set-style(
    mark: (fill: black, scale: 2),
    stroke: (thickness: 0.4pt, cap: "round"),
    angle: (
      radius: 0.3,
      label-radius: .22,
      fill: green.lighten(80%),
      stroke: (paint: green.darken(50%))
    ),
    content: (padding: 1pt)
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
      content("lend.start", [#text(size: 6pt)[$tau_"end"$]],anchor: "north")

      // Draw grid
      for i in t_grid {
        line((i, -inc+cord_start.last()), (i, inc+cord_start.last()))    
      }

      // Deal with the marks/events
      let event_list = ()
      for t in range(0, time_values.len()) {
        event_list.push((name: "v" + str(t), value: time_values.at(t), mformat: $T_( #(t+1) )$))
      }
      for v in event_list {
        line((v.value + cord_start.first(), -2*inc+cord_start.last()), (v.value+cord_start.first(),2*inc+cord_start.last()), name: v.name)
        
        content(v.name + ".start", [#text(size: 6pt)[#v.mformat]], anchor: anchor)
      }
  }
    for v in (2,4) {
        line((v, 0.75), (v, 1.25), stroke: red)
    }
    // Deal with the marks/events
    
    let grid2 = (1,1.7, 2.4,2.8)
    
    group({time_grid((0,1),(5,1), grid2, anchor: "north-east")})
    set-style(mark: (end: ">", scale: 0.5))
    bezier((1,1.25), (2,1.25),(1.5,2.4), stroke: blue)
    bezier((1.7,0.75), (2,0.75), (1.85,0.25), stroke: blue)
    bezier((2.4,1.25), (4,1.25), (3,2), stroke: blue)
        bezier((2.8,0.75), (4,0.75), (3.4,0.25), stroke: blue)
}), caption:  [The "usual" approach where time is discretized. Each event time and its corresponding mark
    is rolled forward to the next time grid point, that is the values of the observations are updated based on the
    on the events occuring in the previous time interval.
]) <fig:discretetimegrid>

#figure(cetz.canvas(length: 0.9cm, {
  import cetz.draw: *

  set-style(
    mark: (fill: black, scale: 2),
    stroke: (thickness: 0.4pt, cap: "round"),
    angle: (
      radius: 0.3,
      label-radius: .22,
      fill: green.lighten(80%),
      stroke: (paint: green.darken(50%))
    ),
    content: (padding: 1pt)
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
      content("lend.start", [#text(size: 6pt)[$tau_"end"$]],anchor: "north")

      // Draw grid
      for i in t_grid {
        line((i, -inc+cord_start.last()), (i, inc+cord_start.last()))    
      }

      // Deal with the marks/events
      let event_list = ()
      for t in range(0, time_values.len()) {
        event_list.push((name: "v" + str(t), value: time_values.at(t), mformat: $T_( #(t+1) )$))
      }
      for v in event_list {
        line((v.value + cord_start.first(), -2*inc+cord_start.last()), (v.value+cord_start.first(),2*inc+cord_start.last()), name: v.name)
        
        //content(v.name + ".start", [#v.mformat], anchor: anchor)
      }
    }
    let eventfun(x, where: "start", anchor: "north",start_y: 0)={
      let event_list = ()
      for t in range(0, x.len()) {
        event_list.push((name: "v" + str(t), value: x.at(t), mformat: $T_( #(t+1) )$))
      }
      for v in event_list {
        line((v.value, -1.5+start_y), (v.value, 1.5+start_y), stroke: red,name: v.name)
        content(v.name + "." + where, [#text(size: 6pt)[#v.mformat]], anchor: anchor)
      }
    }

    rect((0,1.5), (2.8,-1.5),fill:gray,stroke:none)
    let grid1 = (2.5,4.4,6.4)
    // Deal with the marks/events
    eventfun(grid1)
    
    let grid2 = (1,1.7, 2.3,2.8)
    eventfun(grid2, where: "end", anchor: "south")
    
    group({time_grid((0,-1),(10,-1), grid1,inc: 0.1,anchor: "south")})
    group({time_grid((0,1),(10,1), grid2)})
}), caption:  [The figure illustrates the sequential regression approach
    given in @rytgaardContinuoustimeTargetedMinimum2022 for two observations:
    Let $t_1 < dots < t_m$ be all the event times in the sample.
    Then, given $mean(Q)[Y | cal(F)_(t_(r))]$,
    we regress back to $mean(Q)[Y | cal(F)_(t_(r-1))]$ (through multiple regressions).
],) <fig:timegridrytgaard>

#figure(cetz.canvas(length: 0.9cm, {
  import cetz.draw: *

  set-style(
    mark: (fill: black, scale: 2),
    stroke: (thickness: 0.4pt, cap: "round"),
    angle: (
      radius: 0.3,
      label-radius: .22,
      fill: green.lighten(80%),
      stroke: (paint: green.darken(50%))
    ),
    content: (padding: 1pt)
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
      content("lend.start", [#text(size: 6pt)[$tau_"end"$]],anchor: "north")

      // Draw grid
      for i in t_grid {
        line((i, -inc+cord_start.last()), (i, inc+cord_start.last()))    
      }

      // Deal with the marks/events
      let event_list = ()
      for t in range(0, time_values.len()) {
        event_list.push((name: "v" + str(t), value: time_values.at(t), mformat: $T_( #(t+1) )$))
      }
      for v in event_list {
        line((v.value + cord_start.first(), -2*inc+cord_start.last()), (v.value+cord_start.first(),2*inc+cord_start.last()), name: v.name)
        
        content(v.name + ".start", [#text(size: 6pt)[#v.mformat]], anchor: anchor)
      }
    }

    rect((0,1.5), (1.7,0.5),fill:gray,stroke:none)
    rect((0,-1.5), (4.4,-0.5),fill:gray,stroke:none)
    let grid1 = (2.5,4.4,6.4)
    // Deal with the marks/events
    
    let grid2 = (1,1.7, 2.3,2.8)
    
    group({time_grid((0,-1),(10,-1), grid1, anchor: "north-east")})
    group({time_grid((0,1),(10,1), grid2, anchor: "north-east")})
}), caption: [The figure illustrates the sequential regression approach
    proposed in this article. For each event $k$ in the sample, we regress back on the history $history(k-1)$.
    That is, given $mean(Q)[Y | history(k)]$,
    we regress back to $mean(Q)[Y | history(k-1)]$.
    In the figure, $k=3$.
],) <fig:eventgrid>

// Let $cumhazard(k, x, t)$ be the cumulative hazard of $x$ of the $(k+1)$'th event at time $t$ given the history up to the $k$'th event.
// We focus on estimating $cumhazard(k, x, t)$ for $k = 0, dots, K$ for $K >= 0$ rather than $Lambda^x (t \| cal(F)_(t -))$.
// Here $cal(F)_(T_k)$ is the information up to the $k$'th event -- a so-called stopping time $sigma$-algebra.
//Each of these $sigma$-algebras can be represented by a fixed number of random variables, so that regression can be applied at each event point. 
First, we assume that at baseline,
we observe the treatment $treat(0)$ and the time-varying covariates
at time 0, $covariate(0)$. We let $pi_0(dot | covariate(0))$ be the density of the baseline treatment given the covariates at time 0
(with respect to some measure $nu_a$) and
$mu_0$ be the density of time-varying covariates at time 0 (with respect to some measure $nu_ell$).

Let $N^a$ be a counting process generating random times at which treatment may change
and denote these times by $T_1^a < T_2^a < dots < T^a_(N^a (tauend))$.
Let $A(t) in cal(A)$ be a càdlàg treatment process
defined with values in a finite set of treatment
options such that $Delta A(t) = A(t) - A(t-) = 0$
for all $t in [0, tauend]$ with $Delta N^a (t) = 0$.
Similarly, let $N^ell$ be a counting process generating random times at which the covariates may change
and denote these times by $T_1^ell < T_2^ell < dots < T^ell_(N^ell (tauend))$.
Let $L(t) in cal(L)$ be a càdlàg covariate process with values in a finite subset of
$RR^d$ defined on the same time interval that only changes at the times $T_1^ell < T_2^ell < dots < T^ell_(N^ell (tauend))$.
We assume that the jump times differ with probability 1.
Moreover, we assume that only a bounded number of events occur for each individual in the time interval $[0, tauend]$ (@assumptionbounded).
We are interested in the cumulative incidence function, so we also observe 
$N^y$ and $N^d$ corresponding to the counting processes for the primary and competing event, respectively.
Finally, let $N^c$ be the counting process for the censoring counting process.
Our the outcome of interest is $Y_tau = I(T <= tau, Delta = y)$, where $T$ is the time of the terminal event and $Delta in {c, y, d}$ is the indicator for which terminal event occurred.
Furthermore, let $event(k)$ be the time of the $k$'th ordered event in the sample, and define
the counting process $N_t = sum_(k = 1)^(K) I(event(k) <= t)$ for the events in the sample.
Then we define, for for Borel measurable $bb(A)$ and $bb(L)$, the counting process measures,
$
    N_t^ell (bb(L)) &= sum_(i = 1)^(N^ell (tauend)) I(T_i^ell <= t, L(T_i^ell) in bb(L)) \
    N_t^a (bb(A)) &= sum_(i = 1)^(N^a (tauend)) I(T_i^a <= t, A(T_i^a) in bb(A))
$
Though the assumptions so far are stated for stochastic processes, we will instead work with random variables that take values in Euclidean spaces.
This is because the processes are assumed to be càdlàg, so that the information about them in the interval $[0, tauend]$ can be represented by a finite number of random variables (@assumptionbounded).
Specifically, we claim that each of the observation can be written in the form
$
    O = (covariate(0), treat(0), event(1), status(1), covariate(1), treat(1), dots, event(K), status(K), covariate(K), treat(K)).
$
where $O tilde P$ and the sample is given by $n$ i.i.d. copies of $O$, i.e., the observations are from a marked point process.
This can be seen by defining recursively,
$
    event(k) &= inf {t > event(k-1): Delta N^x_t > 0 "for some" x in {a, ell, c, d, y}}, \
    status(k) &= cases(x "if" Delta N_(event(k))^x != 0 "for " x in {a, ell, c, d, y} "and" event(k-1) < oo "and" status(k-1) in {a, ell},
    emptyset "otherwise") \
    covariate(k) &= cases(
        L(T^ell_i) "if" status(k) = ell "and" event(k) = T^ell_i "for some " i, \
       covariate(k-1) "if" status(k) = a,
       emptyset "if" status(k) in {c, y, d}
       ) \
        treat(k) &= cases(
                A(T^a_i) "if" status(k) = a "and" event(k) = T^a_i "for some " i, \
                treat(k-1) "if" status(k) = ell,
                emptyset "if" status(k) in {c, y, d}
                )
$
The history up to the $k$'th event (and including) can be defined recursively by
$
    cal(F)_(T_((0))) := history(0) = sigma(covariate(0), treat(0))
$
for $k = 0$. For $k > 0$, the history#footnote[Formally, the $sigma$-algebra is not usually defined this way, but because we are using the natural filtration as defined in @thm:jointdensity, the usual definition agrees with this one (see Exercise 4.5.1 of @jacobsen2006point).] is
represented by
$
    history(k) = sigma((event(k), status(k), covariate(k), treat(k))) or history(k-1),
$
and in fact $history(K) = sigma(O)$.

@thm:jointdensity shows that if we use the natural filtration,
we can take the intensities to be given by @intensity.
This is important as we consider interventions of the intensity of the form given by @intensity.

#theorem("Distribution of the events and marks")[
    Let $densitytrt(event(k), dot, k-1)$ be the density of the regular conditional distribution of $treat(k)$ given $status(k) = a, event(k), covariate(k-1), treat(k-1), event(k-1) dots, treat(0), covariate(0)$ with respect to the measure $nu_a$.
    Similarly, let $densitycov(t, dot, k-1)$ be the density of the regular conditional distribution of $covariate(k)$ given $status(k) = ell, event(k), covariate(k-1), treat(k-1), event(k-1) dots, treat(0), covariate(0)$ with respect to the measure $nu_ell$.
    Let $hazard(x, t, k-1)$ be the cause-specific hazard of the $x$'th $event(k)$ given $covariate(k-1), treat(k-1), event(k-1) dots, treat(0), covariate(0)$
Then, these are indeed the functions such that
    #math.equation(block: true, numbering: "(1)")[
            $
    lambda_t^ell (bb(L)) &= hazard(ell, t, N_(t-)) integral_(bb(L)) densitycov(t,x, N_(t-)) nu_ell (upright(d) x) \
        &= sum_(k=1)^(K-1) hazard(ell, t, k-1) integral_(bb(L)) densitycov(t,x, k-1) nu_ell (upright(d) x) I_((event(k-1), event(k)]) (t) \
        & \
        lambda_t^a (bb(A)) &= hazard(a, t, N_(t-)) integral_(bb(A)) densitytrt(t,x, N_(t-)) nu_a (upright(d) x) \
        &= sum_(k=1)^(K-1) hazard(a, t, k-1) integral_(bb(A)) densitytrt(t,x, k-1) nu_a (upright(d) x) I_((event(k-1), event(k)]) (t) \
        & \
    lambda_t^x &= hazard(x, t, N_(t-)) = sum_(k=1)^(K) hazard(x, t, k-1) I_((event(k-1), event(k)]) (t), x in {c, y, d}
$
    ] <intensity>
    are the $cal(F)_t$-intensities#footnote[$N_t^x (B) - integral_0^t lambda_s^x (B) upright(d) s$ is an $cal(F)_t$ martingale
        for all Borel measurable sets $B$. ] of the respective counting process measures, where $cal(F)_t$ is the filtration generated by all considered processes up to time $t$, meaning that $cal(F)_t = sigma((N_t^ell (bb(L)), N_t^a (bb(A)), N_t^y, N_t^d, N_t^c) | t >= 0, bb(L) subset.eq cal(L), bb(A) subset.eq cal(A))$.

    Conversely, given the functions in @intensity, we have for Borel measurable sets $bb(L) in cal(L) union {emptyset}$, and $bb(A) in cal(A) union {emptyset}$,
    and under appropriate uniform integrability conditions on the intensity measure#footnote[See the Optional Sampling Theorem in Theorem B.0.12 of @jacobsen2006point.] that
    #math.equation(block: true, numbering: "(1)")[
        $
            &P(event(k) <= s, status(k) = x, covariate(k) in bb(L), treat(k) in bb(A) | history(k-1)) \
                &= integral_0^s underbrace(exp(-sum_(x=y, d, ell, a, c) integral_(0)^(t) hazard(x, s, k-1) upright(d) s), "probability of surviving up to" t.) underbrace(hazard(x, t, k), "probability that it was an event of type "x) \
                &( underbrace(integral_(bb(L)) densitycov(t, x, k-1) nu_ell (upright(d) x), "probability of" covariate(k) in bb(L) "given " status(k) = ell "and" event(k) = t) I(x=ell, treat(k-1) in bb(A)) +  \
                    &+underbrace(integral_(bb(A)) densitytrt(t, x, k-1) nu_a (upright(d) x), "probability of" treat(k) in bb(A) "given " status(k) = a "and" event(k) = t) I(x=a, covariate(k-1) in bb(L)) + I(x in {d, y, c}, emptyset in bb(L), emptyset in bb(A))) upright(d) t.
        $] <jointdensity>
    whenever $status(k-1) in {a, ell}$ and $event(k-1) < oo$.
] <thm:jointdensity>
#proof[
    The theorem is an appropriate extension of Proposition II.7.1 of @andersenStatisticalModelsBased1993 to the multivariate marked point process setting.
First note that we can write, 
$
    N^a_t (bb(A)) = sum_(k = 1)^(K-1) I(event(k) <= t, status(k) = a, treat(k) in bb(A))
$
which we can extend to 
$
    N^a_t (bb(L) times bb(A)) = sum_(k = 1)^(K-1) I(event(k) <= t, status(k) = a, treat(k) in bb(A), covariate(k-1) in bb(L))
$
Similarly, we can define $N^ell_t (bb(L) times bb(A))$. Moreover, we can write
$
    N^x_t (bb(L) times bb(A)) = sum_(k = 1)^(K) I(event(k) <= t, status(k) = x, emptyset in bb(A), emptyset in bb(L))
$
for $x in {c, y, d}$. Define now the counting process
$
    N_t ({x} times bb(L) times bb(A)) = N^x_t (bb(L) times bb(A))
$
    and note that $cal(F)_t = sigma (N_t (bb(X) times bb(L) times bb(A)) | t >= 0, bb(X) subset.eq {ell,y,a,d,c}, bb(L) subset.eq cal(L) union {emptyset}, bb(A) subset.eq cal(A) union {emptyset})$.

    Assume that the conditional distributions of the marks and event times are given as in the theorem.
    Then an intensity measure is given by @intensity by Theorem 4.4.1 of @jacobsen2006point or section 1.10 of @last1995marked
    or in the counting process setting Proposition II.7.1 of @andersenStatisticalModelsBased1993 for the marked point process $N_t$.
    
    Conversely, suppose that the intensity measures are given as in @intensity.
    Then, 
#math.equation(block: true, numbering: "(1)")[$
        &lambda_t (bb(X) times bb(L) times bb(A)) \
            &= hazard(ell, t, N_(t-)) integral_(bb(L)) densitycov(t,x, N_(t-)) nu_ell (upright(d) x) I(ell in bb(X), treat(N_(t-)) in bb(A)) \
            &+ hazard(a, t, N_(t-)) integral_(bb(A)) densitytrt(t,x, N_(t-)) nu_a (upright(d) x) I(a in bb(X), covariate(N_(t-)) in bb(L)) \
            &+ hazard(x, t, N_(t-)) I(d in bb(X) or y in bb(X) or c in bb(X), emptyset in bb(L), emptyset in bb(A))
$] <jointintensity>
    is an intensity measure for the marked point process $N_t$.
    This means that the truncated counting measure $""_event(k-1) N_(t) ({x} times bb(L) times bb(A)) = N_(t) ({x} times bb(L) times bb(A)) - N_(t and event(k-1)) ({x} times bb(L) times bb(A))$
    has the intensity measure
    $
        ""_event(k-1) lambda_t ({x} times bb(L) times bb(A)) = lambda_t ({x} times bb(L) times bb(A)) I_((event(k-1),oo)) (t).
    $
    see e.g., Proposition II.4.2 of @andersenStatisticalModelsBased1993 or p. 308 of @jacobsen2006point.
    Thus,
    $
        N_t^((k)) ({x} times bb(L) times bb(A)) &:= I(event(k) <= t, status(k) = x, covariate(k) in bb(L), treat(k) in bb(A)) \
            &=""_event(k-1) N_(t) ({x} times bb(L) times bb(A)) - ""_event(k) N_(t) ({x} times bb(L) times bb(A))
    $
    has the intensity measure $lambda_t ({x} times bb(L) times bb(A)) I_((event(k-1),event(k)]) (t)$, i.e.,
    
    #math.equation(block: true, numbering: "(1)")[
        $
           N_t^((k)) ({x} times bb(L) times bb(A)) - integral_0^(t) lambda_s ({x} times bb(L) times bb(A)) I_((event(k-1),event(k)]) (t) upright(d) s
        $ 
    ] <mg>
    
    is an $cal(F)_(t)$-martingale.
    By the Optional Sampling Theorem,
    $
        mean(P) [N_(t)^((k)) ({x} times bb(L) times bb(A)) | history(k-1)] &= mean(P) [N_(t and event(k))^((k)) ({x} times bb(L) times bb(A)) | history(k-1)]\
            &= mean(P) [integral_0^(t and event(k)) lambda_s ({x} times bb(L) times bb(A) | history(k-1)) I_((event(k-1),event(k)]) (s) upright(d) s | history(k-1)] \
            &= mean(P) [integral_0^(t) lambda^x_s ( bb(L) times bb(A) | history(k-1)) I_((event(k-1),event(k)]) (s) upright(d) s | history(k-1)] \
            &= integral_0^(t) lambda^x_s ( bb(L) times bb(A) | history(k-1)) mean(P) [I_((event(k-1),event(k)]) (s) | history(k-1)]  upright(d) s  \
            &= integral_0^(t) lambda^x_s ( bb(L) times bb(A) | history(k-1)) P(event(k) >= t | history(k-1))  upright(d) s  \
    $
    Here use @jointintensity and that $N_(t-) = k-1$ if $event(k-1) < t <= event(k)$.
    Hence,
    $
        P(event(k) <= t | history(k-1)) &=
        mean(P) [N_(t)^((k)) ({y,c,d,a,l} times cal(L) union {emptyset} times cal(A) union {emptyset}) | history(k-1)] \
            &= integral_0^(t) sum_(x=a,l,y,c,d)lambda^x_s ( cal(L) union {emptyset} times cal(A) union {emptyset} | history(k-1)) P(event(k) >= t | history(k-1))  upright(d) s  \
            &= integral_0^(t) sum_(x=a,l,y,c,d)lambda^x (s | history(k-1)) P(event(k) >= t | history(k-1))  upright(d) s  \
    $
    yielding $P(event(k) > t | history(k-1)) = 1 - integral_0^(t) sum_(x=a,l,y,c,d)lambda^x (s | history(k-1)) P(event(k) > t | history(k-1))  upright(d) s$
    for which $P(event(k) > t | history(k-1)) = exp(-sum_(x=a,l,y,c,d) integral_0^(t) lambda^x (s | history(k-1)) upright(d) s)$ is the only solution. 
]

// Show existence of functions such that there is a version with lambda^ell (t | cal(F)_(N_t-)) integral_(bb(L)) mu_t (x | cal(F)_(N_t-)) nu_ell (upright(d) x) \
// Apply now Theorem II.7.1 (first part) to get the intensity for the "point" process


// Let $N_t = sum_(k = 1)^(K) I(event(k) <= t)$ be the counting process for the events in the sample.
// We assume that the random counting measure given by
// $
//     N_t (bb(X) times bb(L) times bb(A)) = sum_(k = 1)^(K) I(event(k) <= t, status(k) in bb(X), covariate(k) in bb(L), treat(k) in bb(A))
// $
// has an intensity measure given by#footnote[For now let us just assume this. I don't know if this is the case in general based on the processes defined in the introduction.].
// #math.equation(block: true, numbering: "(1)")[$
//         &lambda_t (bb(X) times bb(L) times bb(A)) \
//             &= hazard(ell, t, N_(t-)) integral_(bb(L)) densitycov(t,x, N_(t-)) nu_ell (upright(d) x) I(ell in bb(X), treat(N_(t-)) in bb(A)) \
//             &+ hazard(a, t, N_(t-)) integral_(bb(A)) densitytrt(t,x, N_(t-)) nu_a (upright(d) x) I(a in bb(X), covariate(N_(t-)) in bb(L)) \
//             &+ hazard(x, t, N_(t-)) I(d in bb(X) or y in bb(X) or c in bb(X), emptyset in bb(L), emptyset in bb(A))
// $] <jointintensity>
// for Borel-measurable sets $bb(X) in cal(X)$, $bb(L) in cal(L) union {emptyset}$, and $bb(A) in cal(A) union {emptyset}$,
// We also assume that $cal(F)_t$ is the natural filtration generated by this counting process measure.

// The densities appearing on the right-hand side of @jointintensity can be interpreted as follows:

// We thus only need to consider the counting process measure,
// $
//     N_t ({x} times bb(L) times bb(A)) = sum_(k = 1)^(K) I(event(k) <= tau, status(k) = x, covariate(k) in bb(L), treat(k) in bb(A))
// $
// which has the intensity
// $
//     & lambda_t ({x} times bb(L) times bb(A)) \
//         &= lambda^ell (t | cal(F)_(t-)) integral_(bb(L)) mu_t (x | cal(F)_(t-)) nu_ell (upright(d) x) I(x=ell, covariate(N_(t-)({a})) in bb(A)) \
//         &+ lambda^a (t | cal(F)_(t-)) integral_(bb(A)) pi_t (x | cal(F)_(t-)) nu_a (upright(d) x) I(x=a, covariate(N_(t-)({l})) in bb(L)) \
//         &+ lambda^x (t | cal(F)_(t-)) I(x in {d,y,c}, emptyset in bb(L), emptyset in bb(A))
// $
// where $N_t ({x}) = N_t ({x} times cal(L) union {emptyset} times cal(A) union {emptyset})$.
// Let $hazard(x, t, k)$ be the hazard of the $x$'th event at time $t$ given the history up to the $k$'th event.
// By Proposition 4.4.1 of @jacobsen2006point,
// the counting intensities are related to the conditional distributions of the marks and times. 

// Given intervention on intensity can we identify the conditional distribution of the marks and times? ^^ above shows other way around Prop 4.4.1

== Example for $K=2$ with $cal(L) = {0, 1}$ and $cal(A) = {0,1}$
In this case, we can represent everything via a multi-state model#footnote("As far as I know the multi-state model framework does not allow the dependence on more than than the latest  (semi-Markov).").
We consider the set of states represented by time 0,
first treatment visit ($a$) set to 1, first treatment visit ($a$) set to 0, first covariate visit ($ell$) set to 1, first covariate visit ($ell$) set to 0, primary event, and competing event.
We consider a world without censoring and consider the figure in @fig:multi-state.

If we represent the first state as time 0 and second state as the first treatment visit ($a$) set to 1.
Then the counting process,
$
    N_12 (t) = I(event(1) <= t, status(1) = a, treat(1) = 1, covariate(1) = covariate(0))
$
has the intensity by @mg given by
$
    hazard(a, t, 0) densitytrt(t, 1, 0)
$
with similar expressions for transitions to the other states.
Moreover, the probability of making this transition before time $t$ is given by @jointdensity.

#figure(diagram(spacing: (12mm, 7.5mm), debug: false, node-stroke: 0.7pt, node-inset: 15pt, label-size: 6pt, {
    let (novisit, treat_visit, treat_visit_2, cov_visit, cov_visit_2, death, comp_risk) = ((0,0), (1.5,-1.5), (1.5,1.5), (-1.5,-1.5), (-1.5,1.5), (0, 3), (0, -3))
    node(novisit, [No patient visit \ $history(0) = (covariate(0), treat(0))$ ])
    node(treat_visit, [1st patient visit ($a$) \ ($history(1)=(covariate(0), treat(0), event(1), status(1), covariate(0), 1)$) ], fill: gray)
    node(treat_visit_2, [1st patient visit ($a$) \ ($history(1)=(covariate(0), treat(0), event(1), status(1), covariate(0), 0))$) ], fill: gray)
    node(cov_visit, [1st patient visit ($ell$) \ ($history(1)=(covariate(0), treat(0), event(1), status(1), 1, treat(0))$)], fill: gray)
    node(cov_visit_2, [1st patient visit ($ell$) \ ($history(1)=(covariate(0), treat(0), event(1), status(1), 0, treat(0))$)], fill: gray)
    node(death, [Primary event])
    node(comp_risk, [Competing event])

    edgemsm(novisit, treat_visit, [$hazard(a, t, 0) densitytrt(t, 1, 0)$])
    edgemsm(novisit, cov_visit, [$hazard(ell, t, 0)  densitycov(t, 1, 0)$], label-pos:0.4)
    edgemsm(novisit, treat_visit_2, [$hazard(a, t, 0) densitytrt(t, 0, 0)$])
    edgemsm(novisit, cov_visit_2, [$hazard(ell, t, 0)  densitycov(t, 0, 0)$])
    
    edgemsm(novisit, death, [$hazard(y, t, 0)$])
    edgemsm(novisit, comp_risk, [$hazard(d, t, 0)$])
    //edgemsmcens(novisit, censoring, [$hazard(c, t, 0)$])

    //edgemsm(treat_visit, treat_visit_2, [$hazard(a, t, 1)$]) 
    //edgemsm(treat_visit, cov_visit_2, [$hazard(ell, t, 1)$], label-pos: 0.8)
    edgemsm(treat_visit, death, [$hazard(y, t, 1)$], label-pos: 0.75)
    edgemsm(treat_visit, comp_risk, [$hazard(d, t, 1)$])
    edgemsm(treat_visit_2, death, [$hazard(y, t, 1)$])
    edgemsm(treat_visit_2, comp_risk, [$hazard(d, t, 1)$], label-pos: 0.75)
    //edgemsmcens(treat_visit, censoring, [$hazard(c, t, 1)$])

    edgemsm(cov_visit, death, [$hazard(y, t, 1)$], label-pos: 0.75)
    edgemsm(cov_visit, comp_risk, [$hazard(d, t, 1)$])
    edgemsm(cov_visit_2, death, [$hazard(y, t, 1)$])
    edgemsm(cov_visit_2, comp_risk, [$hazard(d, t, 1)$], label-pos: 0.75)
}), caption: [A multi-state model for $K=2$ with $cal(L) = cal(A) = {0, 1}$.])
<fig:multi-state>

= A pragmatic approach to continuous-time causal inference
One classical causal inference perspective requires that we know how the data was generated up to unknown parameters (NPSEM) #citep(<pearlCausalityModelsReasoning2009>).
DAGs are not the most used way of representing the data generating mechanism in the continuous-time setting,
but for the event times, we can draw a figure representing the data generating mechanism which is shown in @fig:dag.
#figure(
    diagram(node-stroke: 0.7pt, node-shape: circle, {
        let (historyprior, inst, historyfuture) = ((1,0), (2.5,0), (4,0))
        let (l0, a0, f1) = ((6, 0), (7, -0.5), (7, 0.5))
        // Define the nodes (variables)
        node(enclose: ((0,-1.5), (4.5,1.5)), // a node spanning multiple centers
            inset: 10pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k > 0$:])
        node(enclose: ((5.5,-1), (8,1)), // a node spanning multiple centers
            inset: 10pt, stroke: teal, fill: green.lighten(90%), snap: -1, align(top + left)[For $k = 0$:])
        dagnode(historyprior, [$historypast(k - 1)$])
        node(inst, [#text(size:6pt)[$(event(k), status(k), covariate(k), treat(k))$]], width: 2cm, height: 2cm)
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
        A DAG for the data generating mechanism.
        The dashed lines indicate multiple edges from the dependencies in the past and into the future.
        Here $historypast(k)$ is the history up to and including the $k$'th event and $historynext(k)$ is the history after and including the $k$'th event.
    ],
) <fig:dag>

#definition("Target parameter")[
    Let $Q$ denote the distribution of an intervention where the random measure
    $lambda^c_t$ and $densitytrt(t,x, N_(t-))$ are replaced by  $lambda^{c,*}_t = 0 "and" densitytrtint(t,x, N_(t-))$.
    We also intervene on the regular conditional distribution of $treat(0)$ given $covariate(0)$ by replacing the density $pi_0$ with $pi^*_0$.
    Then our target parameter is: $Psi_(tau)(Q) = mean(Q) [sum_(k=1)^K I(event(k) <= tau, status(k) = y)]$.
]

For this definition, we need a notion of no unobserved confounding, but this is not discussed in the context of continuous-time causal inference (but see e.g., @roeysland2024).
We also need notion of positivity, which we also won't discuss here. 

Also note that according to our example with multi-state models with $cal(A)= cal(L) = {0,1}$: If $T$ is the time to
the first transition into the primary event or competing event state and 𝐷 corresponds to the terminal event type,
then our target parameter does indeed correspond to the cumulative incidence function at
time $tau$ with $T$ and $D$ being the time-to-event and the status, respectively. The target parameter simply
summarizes that this can either happen as the first or second event.

We first state and prove a formula for at target parameter that is not causal, but we will use it to identify the causal parameter.

// should just be identification not of conditional densities
#theorem[
    Let $macron(Q)_K = I(event(K) <= tau, status(K) = y)$ and
    $macron(Q)_k = mean(P) [sum_(j=k+1)^K I(event(j) <= tau, status(j) = y) | history(k)]$.
    Then,
    $
        macron(Q)_(k-1) &= mean(P) [I(event(k) <= tau, status(k) = ell) macron(Q)_(k)(treat(k-1), covariate(k), event(k), status(k), history(k-1)) \
            &+ I(event(k) <= tau, status(k) = a) mean(P) [macron(Q)_(k)(treat(k), covariate(k-1), event(k), status(k), history(k-1)) | event(k), status(k), history(k-1)] \
            & + I(event(k) <= tau, status(k) = y) mid(|) history(k-1)]
    $
    for $k = K, dots, 1$.
    Thus, $mean(P) [sum_(k=1)^K I(event(k) <= tau, status(k) = y)]= mean(P) [macron(Q)_0]$.
]<thm:parameter>

#proof[
    We find
    $
        macron(Q)_k &= mean(P) [sum_(j=k+1)^K I(event(j) <= tau, status(j) = y) | history(k)] \
            &= mean(P) [mean(P) [mean(P) [sum_(j=k+1)^K I(event(j) <= tau, status(j) = y)  | history(k+1)]  | event(k+1), status(k+1), history(k) ] | history(k)] \
            &= mean(P) [I(event(k+1) <= tau, status(k+1) = y) \
                &#h(2cm)+ mean(P) [mean(P) [sum_(j=k+2)^K I(event(j) <= tau, status(j) = y) | history(k+1)]  | event(k+1), status(k+1), history(k)]
                mid(|) history(k)] \
            &= mean(P) [I(event(k+1) <= tau, status(k+1) = y) \
                &+ I(event(k+1) <= tau, status(k+1) = a) mean(P) [mean(P) [sum_(j=k+2)^K I(event(j) <= tau, status(j) = y) | history(k+1)]  | event(k+1), status(k+1), history(k)] | history(k)] \
            &+ mean(P) [I(event(k+1) <= tau, status(k+1) = ell) mean(P) [sum_(j=k+2)^K I(event(j) <= tau, status(j) = y) | history(k+1)] | history(k)] \
    $
    by the law of iterated expectations and that
    $
        (event(k) <= tau, status(k) = y) subset.eq (event(j) <= tau, status(j) in {a, ell})
    $
    for all $j = 1, dots, k-1$ and $k = 1, dots, K$.
] 

#theorem("Identification via g-formula")[
    Let $Qbar(k) = Qbarmiss(k)(Q)$ be defined as in the previous theorem for $Q$. 
    Then, we can identify $Qbar(k)$ via the intensities as
#math.equation(block: true, numbering: "(1)")[$
    Qbar(k) &= commonintegral(k, tau, survivalfunction(k, s, {ell, a, d, y}) hazard(a, s, k)  \
        & #h(3cm) times (integral_(cal(A)) Qbar(k+1) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (upright(d) a_k) ), s) \
        &+ commonintegral(k, tau, survivalfunction(k, s, {ell, a, d, y}) hazard(ell, s, k) \
            & #h(3cm) times (integral_(cal(L)) Qbar(k+1) (l_k, treat(k-1), s, ell, history(k)) densitycov(s, l_k, k) nu_L (upright(d) l_k) ), s) \
        &+ commonintegral(k, tau, survivalfunction(k, s, {ell, a, d, y}) hazard(y, s, k), s) \
$] <eq:cuminc>
Alternatively, we can apply inverse probability of censoring weighting to obtain
    #math.equation(block: true, numbering: "(1)")[$
        Qbar(k-1) &= mean(P) [I(event(k) <= tau, status(k) = ell)/(exp(-integral_(event(k-1))^(event(k)) lambda^c (s | history(k)) upright(d) s)) Qbar(k)(treat(k-1), covariate(k), event(k), status(k), history(k-1)) \
            &#h(1.5cm) + I(event(k) <= tau, status(k) = a) /(exp(-integral_(event(k-1))^(event(k)) lambda^c (s | history(k)) upright(d) s)) \
            &#h(2.5cm) times integral Qbar(k) (a_k, covariate(k-1), event(k), status(k), history(k-1)) densitytrtint(event(k), a_k, k) nu_A (upright(d) a_k) \
            &#h(1.5cm) + I(event(k) <= tau, status(k) = y) /(exp(-integral_(event(k-1))^(event(k)) lambda^c (s | history(k)) upright(d) s)) mid(|) history(k-1)]
    $] <eq:ipcw>
    for $k = K-1, dots, 1$.
    Then, 
    $
        Psi_tau lr((Q)) = mean(P) [ integral  Qbar(0) (a, covariate(0)) nu_A (upright(d) a)].
    $
]
#proof[The theorem is an immediate consequence of @thm:jointdensity and @thm:parameter (the sets $(event(k) <= t, status(k) = x, covariate(k) in bb(L), treat(k) in bb(A))$ fully determine the regular conditional distribution of $(event(k), status(k), covariate(k), treat(k))$ given $history(k-1)$).]

Interestingly, @eq:cuminc corresponds exactly with the target parameter of @rytgaardContinuoustimeTargetedMinimum2022
and @gill2023causalinferencecomplexlongitudinal by plugging in the definitions of $Qbar(k)$ and simplifying
(to be shown).

= Implementation of the Iterative Conditional Expectations formula

We assume that $K_tau$ is the 1 + the maximal number of
non-terminal events that occur before time $tau$. For now, we assume
that this is number is fixed and does not depend on the sample.
Let $tilde(Y)_k (t) = I (event(k-1) < t <= event(k))$.

For $k = K_tau - 1, dots, 0$:
- We want a prediction function $Qbar(k)$ of the history up to the $k$'th event, that is
  $Qbar(k) : cal(H)_k --> RR$, given that we have one for the $(k + 1)$’th event, i.e.,
  $Qbar(k+1) : cal(H)_k --> RR$ (note that for $k = K_tau$, we have
  $Qbar(K_tau) = I (event(K_tau) <= tau, status(K_tau) = y)$.).
  We consider the data set $cal(D)_(k, n)$ that is obtained from the
  original data $cal(D)_n$ by only considering the observations that have
  had $k$ non-terminal events, that is
  $status(k) in {a, ell}$ for $j = 1, dots, k$. On this data:
    - We estimate $hazard(c, dot, k + 1)$ by using $event(k + 1)$ as the time-to-event and $status(k+1)$ as the event
      indicator on the data set $cal(D)_(k, n)$, regressing on
      $history(k) = (covariate(k), treat(k), event(k), status(k), dots, covariate(0), treat(0))$#footnote[ We abuse the notation a bit by writing $history(k)$
          here, but it is actually a $sigma$-algebra.]
  We are now able provide estimated values for the integrand in @eq:ipcw.
  These values are provided on the smaller data set $cal(D)_(k, n, tau)$
  of $cal(D)_(k, n)$ where we only consider the observations with
  $event(k) <= tau$. This is done as follows:
    1. For observations in $cal(D)_(k, n, tau)$ with $status(k + 1) = ell$ and $event(k + 1) <= tau$, use the previous function
       to predict values $Qbar(k+1)(covariate(k+1), treat(k), event(k+1), status(k+1), history(k))$.
    2. For observations in $cal(D)_(k, n, tau)$ with $status(k + 1) = a$ and $event(k + 1) <= tau$, 
       integrate using the previous function $integral_(cal(A)) Qbar(k+1)(covariate(k), a_k, event(k+1), status(k+1), history(k)) densitytrtint(event(k+1), a_k, k) nu_A (upright(d) a_k)$.
       If for example the intervention sets the treatment to 1, then
       $integral_(cal(A)) Qbar(k+1)(covariate(k), a_k, event(k+1), status(k+1), history(k)) densitytrtint(event(k), 1, k) nu_A (upright(d) a_k) = Qbar(k+1)(covariate(k), 1, event(k), status(k), history(k))$.
       This gives predicted values for this group.
    3. For observations in $cal(D)_(k, n, tau)$ with $status(k + 1) = y$ and $event(k + 1) <= tau$, simply put the values equal to 1.
    4. For all other observations put their values equal to 0.
  For all the observations, divide the corresponding values by
  estimates of censoring survival function $exp(-integral_(event(k))^(event(k+1)) lambda^c (s | history(k)) upright(d) s)$.
  We then regress the values on $history(k) = (covariate(k), treat(k), event(k), status(k), dots, covariate(0), treat(0))$.
  From this regression, we set $Qbar(k)$ to be the predicted values of the
  function from the regression.
- If $k = 0$: We estimate the target parameter via
  $bb(P)_n [sum_(k=1)^(K_tau) Qbar(0) (dot, a_0) nu_A (upright(d) a_0)]$.

*Note*: The $Qbar(k)$ have the interpretation of the
heterogenous causal effect after $k$ events.

For now, we recommend @eq:ipcw for estimating $Qbar(k)a$: For estimators of
the hazard that are piecewise constant, we would need to compute
integrals for each unique pair of history and event times occurring
in the sample at each event $k$. On the other hand, the IPCW approach is very
sensitive to the specification of the censoring distribution. Something
very similar can be written down when we use @eq:cuminc.

== Alternative nuisance parameter estimators
An alternative is to estimate the entire cumulative hazards $Lambda^x$ at once instead of having $K$ separate parameters:
There are very few methods for marked point process estimation but see @liguoriModelingEventsInteractions2023 for methods mostly based on neural networks
or @weissForestBasedPointProcess2013 for a forest-based method. As a final alternative, we can use temporal difference learning to avoid iterative estimation of $macron(Q)^a, tilde(Q)$ @shirakawaLongitudinalTargetedMinimum2024.
Most point process estimators are actually on the form given in terms of @intensity. 

= The efficient influence function (needs to be updated)
We want to use machine learning estimators of the nuisance parameters,
so to get inference we need to debias our estimate with the efficient influence function, e.g., double/debiased machine learning @chernozhukovDoubleMachineLearning2018 or
targeted minimum loss estimation @laanTargetedMaximumLikelihood2006. We use @eq:ipcw for censoring to derive the efficient influence function, because it will contain fewer martingale terms.
Let $N_k^c (t) = N_t ({c} times cal(L) union {emptyset} times cal(A) union {emptyset})$.

#theorem("Efficient influence function")[
    Let $Qbar(k) (u) := I(eventcens(k) <= u, statuscens(k) != c)/(exp(-integral_(event(k-1))^(event(k)) lambda^c (s | history(k)) upright(d) s)) Qtilde(k+1) (event(k+1), status(k+1), history(k))$
    for $u <= tau$. The efficient influence function is given by
    #text(size: 7.5pt)[$
        phi_tau^*(P) &= sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), treat(j), j-1)))^(I(status(j) = a))
        (I (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) upright(d) s)) \
            & times lr(\[I (k < K) (I (status(k) in {ell, a}, event(k) <= tau)) / (exp(- integral_(event(k-1))^(event(k)) hazard(c, s, j-1) upright(d) s))
            lr(\[Qbar(k) (tau, history(k)) - Qtilde(k) (event(k), status(k), history(k - 1)) \]) \
            & #h(2em) + (I (status(k) != c, event(k) <= tau)) / (exp(- integral_(event(k-1))^(event(k)) hazard(c, s, j-1) upright(d) s))
            Qtilde(k) (event(k), status(k), history(k - 1)) - Qbar(k - 1) (tau, history(k-1)) \
            & #h(2em) + integral_(event(k - 1))^tau (Qbar(k - 1) (tau, history(k -1)) - Qbar(k - 1) (u, history(k -1))) 1/(exp(- integral_0^u sum_(x=a, ell, d, y, c) hazard(x, s, k- 1) upright(d) s))
            (N_k^c (upright(d) s) -  tilde(Y)_(k - 1) (s) hazard(c, s, k-1) upright(d) s) \]) \
            &+ integral Qtilde(1) (a, covariate(0)) nu_A (upright(d) a)- Psi_tau (P)
    $]
    (we take the empty sum to be zero and define $T_0 = 0$, $status(0) = a$ and $history(-1) = L(0)$.)
]

For now, we recommend using the one step estimator and not the TMLE because the martingales are computationally intensive to estimate.
This means that multiple TMLE updates may not be a good idea. 

= Data-adaptive choice of $K$
In practice, we will want to use $K_tau$ to be equal to 1 + maximum number of non-terminal events up to $tau$ in the sample. 
It turns out, under the boundedness condition of the number of events,
that an estimator that is asymptotically linear with efficient influence function $phi_tau^*(P) (max_i kappa_i (tau))$
is also asymptotically linear with efficient influence function $phi_tau^*(P) (K_tau)$
where $K_tau$ is the last event point such that $P(kappa_i (tau) = K_tau) > 0$.

Sketch: We want to use $K = K_n = max_i kappa_i (tau)$.
If we can do asymptotically and efficient inference for $K_n$, then we can also do it for a limiting $K_n <= K$.
Assume that the estimator is asymptotically linear with efficient influence function $phi_tau^*(P) (K_n)$.
Then by Assumption 1, there exists a $K_lim$ which is the last point such that $P(K_n = K_lim) > 0$.
Then, $K_n$ converges to $K_lim$ (by independence), and moreover, under standard regularity conditions such as strict positivity,
$
    (bb(P)_n-P) ( phi_tau^*(P) (K_n) - phi_tau^*(P) (K))
$ is $o_P(n^(-1/2))$, so if have asymptotic linearity in terms of $phi_tau^*(P) (K_n)$, then we automatically have it
for the original estimator for $phi_tau^*(P) (K_lim)$

= Issues relating to rare patient histories (postponed)
Consider the following table representing example data:

#figure(
table(
  columns: 7,
    [$k$], [0], [1], [2], [3], [4], [5],
    [$tilde(Y)_k (tau)$],   [10000], [8540], [5560], [2400], [200], [4],
    [$Delta treat(k)$],     [6000],  [3560], [1300],  [100],  [2], [NA],
    [$Delta covariate(k)$], [2540],  [2000], [1100], [100],  [2], [NA]
))
== Pooling

Some people have complex histories. There may be very few of these people in the sample,
so how do we do estimate the cause-specific hazard for the censoring in, say, the first step?
In the artificial data example, there are only 4 people at the last time point. 

We propose to pool the regressions across event points:
Let us say that we want to estimate the cause-specific hazard for the censoring at event $k+1$
among people who are at risk of being censored at the $k+1$'th event, that is
they either had a treatment change or a covariate change at their $k$ event.
If this population in the sample is very small, then we could do as follows.
We delete the first event for these observations. Then
the number of covariates is reduced by one, so we have the same number of covariates
as we did for the people who are at risk of having an event at the $k$'th event.
We combine these two data sets into one and regress the cause-specific hazard for the censoring at event "$k$".
This provides a data set with correlated observations,
which likely is not biased as we are not interested in variance estimation for parameters appearing in the regression.

To estimate the regression for the time-varying covariates, one could do:
- Not intervene on the last two or three time points, letting certain parts of the data generating mechanism be observational,
  that is $densitytrtint(t, dot, j) = densitytrt(t, dot, j)$ for $j = 4, 5$.
- Another is to make a Markov-like assumption in the interventional world, i.e.,
  $
      mean(Q) [ sum_(j=1)^3 I(event(j) <= tau, status(j) = y) | history(0)] = mean(Q) [sum_(j=6)^8 I(event(j) <= tau, status(j) = y) | history(5)]
  $
  So we separately estimate the target parameter on the left hand side and use it to estimate the one on the right when we need to,
  pooling the data from the last three events with the data from the first three events.

Doing this adaptively leads to data-adaptive target parameter #citep(<hubbard2016statistical>).

// The most unfortunate situation-wise is that:
// #figure(
// table(
//   columns: 3,
//     [$k$], [0], [1], 
//     [$tilde(Y)_k (tau)$],   [10000], [8004],
//     [$Delta treat(k)$],     [8000],  [...],
//     [$Delta covariate(k)$], [4],  [...]
// ))
// In this case, we can forget about using iterative regression -- what we used previously is
// that the only point of sparsity was after many events. 
// Here we would need to estimate the conditional density of $densitycov(t, dot, 1)$ instead of regressing
// -- this could be done by once again pooling, but may be very hard to do computationally because the estimation of a conditional
// density is much, much harder than regression.

Other possible methods are:

- Use an estimation procedure that is similar to @shirakawaLongitudinalTargetedMinimum2024 or use hazards which are estimated all at once.

- Bayesian methods may be useful since they do not have issues with finite sample size. They are also a natural way of dealing with the missing data problem.
  However, nonparametric Bayesian methods are not (yet) able to deal with a large number of covariates.

== Other ideas
Some other issues are that the covariates are (fairly) high dimensional.
This may yield issues with regression-based methods. 

- Use Early-stopping cross-validation described as follows:
  First fit models with no covariates.
  Then we fit a model with the covariates from the last event.
  Determine if this is improves model fit via cross-validation and then we move on to the two latest changes and so on.
  Stop when the model fit does not improve. Theorem 2 of @schulerSelectivelyAdaptiveLasso2022 states that the convergence rates for an empirical risk minimizer are preserved.
  CTMLE also does something very similar #citep(<van2010collaborative>).
  This way, we may only select variables that are important in the specification of the treatment and outcome mechanism.

== Topics for further research

Interestingly, $integral Qbar(0) (a, covariate(0)) nu_A (upright(d) a)$ is a heterogenous causal effect.
Can we estimate heterogenous causal effects in this way?

Time-fixed time-varying treatment could probably be interesting within
a register-based study since it may be easier to define treatment in an interval
rather than two define on, each time point, if the patient is on the treatment or not.

It may also sometimes be the case that some time-varying covariates
are measured regularly instead of at subject-specific times.
In this case, we may be able to do something similar to the above.

#bibliography("references/ref.bib",style: "apa")
