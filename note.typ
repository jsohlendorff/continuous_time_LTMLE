#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices

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
// JOHAN: consider We let $(Omega, cal(F), cal(M))$ be a statistical experiment ...
We let $(Omega, cal(F), P)$ be a probability space on which all processes
and random variables are defined.

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
Thus, we have observations from a jump process $alpha(t) = (N^a (t), A (t), N^ell (t), L(t), N^y (t), N^d (t))$,
and the natural filtration $(cal(F)_t)_(t>=0)$ is given by $cal(F)_t = sigma (alpha(s) | s <= t) or cal(F)_0$.
Let $event(k)$ be the $k$'th ordered jump time of $alpha$, that is $T_0 = 0$ and $event(k) = inf {t > event(k-1) | alpha (t) != alpha (event(k-1))} in [0, oo]$ be the time of the $k$'th event
and let $status(k) in {y, d, a, ell}$ be the status of the $k$'th event, i.e., $status(k) = x$ if $Delta N^x (event(k)) = 1$, so that
//JOHAN: why emphasize these 3 conditions? they seem not very surprising 
1. each $event(k)$ is a $cal(F)_t$ stopping time.
2. $event(k) < event(k+1)$ if $event(k) < oo$.
3. $event(k+1) = oo$ if $event(k) = oo$ or $status(k-1) in {y, d}$.

//We also impose the condition that the last event has to be a terminal event, i.e., $status(K) = y$ or $d$.
We let $treat(k)$ ($covariate(k)$) be the treatment (covariate values) at the $k$'th event, i.e., $treat(k) = A(event(k))$ if $status(k) = a$ ($covariate(k) = L(event(k))$ if $status(k) = ell$)
and $treat(k) = A(event(k-1))$ ($covariate(k) = L(event(k-1))$) otherwise.
To the process $(alpha(t))_(t>=0)$, we associate the corresponding random measure $N^alpha$ on $(RR_+ times ({y, d, a, ell} times {0,1} times cal(L)))$ by
//JOHAN: consider \mathrm d instead of d in the following display
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
stopping time $event(k)$ fulfills that $history(k)= sigma( treat(k), covariate(k), event(k), status(k)) or history(k-1)$. $history(k)$ represents the information up to the $k$'th event.
We will interpret $history(k)$ as a random variable instead of a $sigma$-algebra, whenever it is convenient to do so and also make the implicit assumption that whenever we condition on $history(k)$,
we only consider the cases where $event(k) < oo$ and $status(k) in {a, ell}$.

We observe $O=history(K) = (event(K), status(K), treat(K-1), covariate(K-1), event(K-1), status(K-1), dots, treat(0), covariate(0)) ~ P in cal(M)$ where
$cal(M)$ is the statistical model, i.e., a set of probability measures. 
// JOHAN: we seem to assume that densitytrt is a stochastic process in t with piecewise constant trajectories
//        also, we implicitely assume that since T(k-1) nothing else has changed which could affect the treatment probability.
//        I find these assumptions more important than current Assumptions 1,2 
Let $densitytrt(t, k)$ be the probability of being treated at the $k$'th event given $status(k) =a, event(k) = t$, and $history(k-1)$.
Similarly, let $densitycov(t, dot, k)$ be the probability measure for the covariate value $status(k) = ell, event(k) = t$, and $history(k-1)$.
Let also $cumhazard(k, x, dif t)$ be the cumulative cause-specific hazard measure #footnote[Let $T in (0, oo]$ and $X in cal(X)$ be random variables. Then the cause-specific cumulative hazard measure is given by
    $Lambda_x (dif t) = bb(1) {P(T >= t} > 0} P(T in dif t, X = x) / P(T >= t)$ (Appendix A5.3 of @last1995marked).] for the $k$'th event of type $x$ given $history(k-1)$.

// JOHAN: until here the style of writing is technical, so why not express the assumptions in a more technical
//        fashion too? also, why is assumption 1 needed, can you make an example where it is not satisfied?
#assumption("Bounded number of events")[
In the time interval $[0, tauend]$ there are at most $K - 1 < oo$ many changes of treatment and
    covariates in total for a single individual. The $K$'th event is terminal. 
] <assumptionbounded>
// JOHAN: is this no jumps in common assumption necessary or mostly for ease of presentation?
#assumption("No simultaneous jumps")[
    The counting processes $N^a$, $N^ell$, $N^y$, $N^d$, and $N^c$ have with probability 1 no jump times in common.
    #footnote[If the resulting martingales $M^x$, are of locally bounded variation, then the processes are orthogonal $[M^x, M^(x')]_t = 0$ for $x != x'$ $P$ -a.s,
        where $[dot, dot]$ is the quadratic covariation process.]
] <assumptionnosimultaneous>

= Causal framework

// JOHAN: elaborate on the definition of g. g seems to operate on A only. need to discuss if g affects N^a because we assume
// that A can only change where N^a changes
// and discuss (briefly) what interventions are of interest (static, dynamic, stochastic) in applications, then say
// that for ease of presentation we assume A to be one-dimensional and A^g(t)=1. is it clear what extensions are covered by the theory?
// i.e., what is the first time where a subject does not follow a stochastic regime?
// Further explain that one is really interesting in contrasts of treatment plans/regimes 
Our overall goal is to estimate the interventional cumulative incidence function at time $tau$,
$
    Psi_tau^g (P) = mean(P) [tilde(N)^y (tau)],
$
// JOHAN: would be good to have g in the notation of the potential outcome but the N notation, N^(g), is overloaded
//        perhaps okay to replace tilde(N)^y by 1{T^g_K < tau, Delta^g_K=y}?
where $tilde(N)^y (t)$ is the potential outcome (a counting process with at most one jump) representing
the counterfactual outcome $N^y (t) = sum_(k=1)^K bb(1) {event(k) <= t, status(k) =y}$ had the treatment
regime $g$, possibly contrary to fact, been followed. For simplicity, we assume that the treatment
regime specifies that $A(t) = 1$ for all $t >= 0$.
This means that treatment is administered
at each visitation time.
In terms of these data, this means that we must have $A(0) = 1$ and $treat(k) = 1$ whenever $status(k) = a$ and $event(k) < t$.
// JOHAN: maybe first define the weight process and then remark that it is càdlàg
We now define the càdlàg weight process $(W (t))_(t>=0)$ given by
$
        W (t) = product_(k=1)^(N_t) ((bb(1) {treat(k) = 1}) / (densitytrt(event(k), k)))^(bb(1) {status(k) = a}) (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0))),
$ <eq:weightprocess>
// JOHAN: better to use n_t instead of N_t?
where $N_t = sum_k bb(1) {event(k) <= t}$ is the number of events up to time $t$,
// JOHAN: the expression "observed data target parameter" is odd. I would define the "target parameter" and then here say that 
//        Psi_tau identifies the target parameter 
and we consider the observed data target parameter $Psi_tau^"obs" : cal(M) -> RR_+$#footnote[Note that by fifth equality of Appendix S1.2 of @rytgaardContinuoustimeTargetedMinimum2022,
    this is the same as the target parameter in @rytgaardContinuoustimeTargetedMinimum2022 with no competing event.]
 given by
$
        Psi_tau^"obs" (P) = mean(P) [N^y (tau) W (tau)].
$ <eq:identification>
// JOHAN: non-martingale is an odd expression. 
We provide both martingale and non-martingale conditions for the identification ($Psi_tau^g (P) = Psi_tau^"obs" (P)$) of the mean potential outcome in @thm:identifiabilitymartingale and @thm:identifiability,
respectively.
// JOHAN: the following 2 sentences need elaboration and may have to be moved to the discussion 
One can also define a (stochastic)
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
We adopt a martingale-based approach for identifying causal effects, following the methodology of @ryalenPotentialOutcomes
#footnote[The overall difference between @ryalenPotentialOutcomes and our exchangeability condition is that the $P$-$cal(F)_t$ compensator $Lambda^a_t ({1})$ is not required to be the $P$-$(cal(F)_t or sigma(tilde(N)^y))$ compensator for $N^a$.].

To this end, we define the stopping time $T^a$ as the time of the first visitation event where the treatment plan is not followed, i.e.,
$
    T^a = inf_(t >= 0) {A(t) = 0} = cases(inf_(k > 1) {event(k) | status(k) = a, treat(k) != 1} "if" A(0) = 1, 0 "otherwise")
$
//JOHAN: can we find a different symbol for T^a to avoid confusion with T_(k)?
Overall $T^a$ acts as a coarsening variable, limiting
the ability to observe the full potential outcome process. An illustration of the consistency condition in @thm:identifiabilitymartingale is provided in @fig:potentialoutcome.
Informally, the consistency condition states that the potential outcome process $tilde(N)^y (t)$
coincides with $N^y (t)$ if the treatment plan has been adhered to up to time point $t$.

// JOHAN: refer to van der Laan and Robins book 
To fully phrase the causal inference problem as a missing data problem,
we also need an exchangeability condition.
// JOHAN: elaborate on this intuition: you write outcome process but mean potential outcome process?
//        and should it be independent of the OBSERVED timing and treatment assignment?
The intuition behind the exchangeability condition in @thm:identifiabilitymartingale
is that the outcome process $tilde(N)^y$ should be
independent of both the timing of treatment visits and treatment assignment,
conditional on observed history.

We also briefly discuss the positivity condition,
which ensures that $(W(t))_(t >= 0)$ is a uniformly integrable martingale
with $mean(P) [W(t)] = 1$ for all $t in [0, tauend]$ by @eq:sde. This guarantees
that the observed data parameter $Psi_tau^"obs" (P)$ is well-defined.

//JOHAN: the transition to this following statement is not smooth: "instead of conditioning" where?
//       you seem to discuss the assumptions of Theo 1 before stating Theo 1
Note that instead of conditioning on the entire potential outcome process in the exchangeability condition,
we could have simply conditioned on a single potential outcome variable $tilde(T)_y := inf {t > 0 | tilde(N)^y (t) = 1} in [0, oo]$#footnote[A competing event occuring corresponds to $tilde(T)_y = oo$]
and included that information at baseline #footnote[Note that $bb(1) {tilde(T)_y <= t} = tilde(N)^y (t)$ for all $t > 0$ because $(tilde(N)^y (t))_(t>=0)$ jumps at most once.].
//#footnote[Note that if $N^y (t)$ and $N^y (t)$ are counting processes for an event of interest and a competing event, respectively.
//then $tilde(T)_y$ is the time of the first event of interest and $T^y$ is the time of the first competing event.
//$bb(1) {T <= t, D = y} = bb(1) {T^y <= t}$.].

We can also state the time-varying exchangeability condition of @thm:identifiabilitymartingale explicitly in terms of the observed data:
Let $cal(H)_(event(k))$ be the corresponding stopping time $sigma$-algebra for the $k$'th event
with respect to the filtration ${cal(H)_t}$ given in @thm:identifiabilitymartingale.
In light of the canonical compensator (@thm:jointdensity (ii)), we see immediately that the exchangeability condition is fulfilled if
$ treat(k) perp tilde(T)_y | event(k), status(k) = a, history(k-1)$
and the cause-specific cumulative hazards for $event(k) | history(k-1), tilde(T)_y$
for treatment visits only depend on $history(k-1)$ and not on $tilde(T)_y$.

Further work is needed to cast this framework into a coarsening at random (CAR) framework (@onrobinsformula).
// JOHAN: the following may be correct but is also a show stopper?
In particular, it is currently unclear whether the parameter $Psi_tau (P)$ depends on the distribution of treatment visitation times and treatment assignment
and whether the identification conditions impose restrictions on the distribution of the observed data process.

// #footnote[It may be shown in
//     contrast that a sufficient condition for the exchangeability condition in @ryalenPotentialOutcomes
//     is that the cumulative cause-specific hazard of $event(k) | cal(H)_(event(k-1)$
//     for treatment visits that assign no treatment do not depend on $tilde(T)_y$,
//     which is actually slightly weaker. If the treatment visitation times are actually not random (i.e., regular),
//     the two stated conditions are the same. //Look into the more general setting.
// ]

//At this point, it is unclear to me if the conditions, unlike coarsening at random (CAR),
//impose restrictions on the observed data process in terms of the observed outcome. //, i.e., is "locally arbitrary" in the sense described by @onrobinsformula.

// JOHAN: this theorem is not for right censored data and  we need to state this here again.
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
       // JOHAN: really only treat(0) and not also treat(t) for t>0?
       perp treat(0) | covariate(0), forall t in (0, tauend].
  $
- *Positivity*: $mean(P) [integral bb(1) {t <= tauend} |zeta(t, m, a, l) - 1| W (t-) N (d (t, m, a, l))] < oo$ and $ mean(P) [W(0)] = 1.$
    //$mean(P) [lim_(t -> oo) W(t)] = mean(P) [W(0)] = 1$ and $mean(P) [W (t)^2] < oo$ for all $t > 0$. #footnote[Most likely, it is sufficient for these properties to hold until $tauend$ and not $oo$, because we don't care about identification after that point. ]
  //$densitytrt(event(k), k) > eta$ and $pi_0 (covariate(0)) > eta$ for all $k in {1, dots, K-1}$ and $t > 0$ for some $eta > 0$ $P$-a.s. #footnote[Probably not the most general condition, but it is sufficient for the proof of the theorem.]    //$W (t) = product_(k=1)^(N_t) ((bb(1) {treat(k) = 1}) / (densitytrt(event(k), k)))^(bb(1) {status(k) = a}) (bb(1) {treat(0) = 1})/ (pi_0 (covariate(0))) < eta$ for all $t>0$ (for simplicity)#footnote[Implying that $mean(P) [W (t)] = 1$ for all $t$].  //fulfills $mean(P) [W (t)] = 1$ for all $t in {0, oo}$ (by monotonicity of $L(t)$ all values in between have mean 1).

// JOHAN: Psi_(t)^g has not been defined yet
Then,
$
    Psi_(t)^g (P) = Psi_t^"obs" (P)
$ for all $t in (0, tauend]$.
] <thm:identifiabilitymartingale>

#proof[
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
While the overall exchangeability condition can be expressed in an alternative form, the consistency condition remains essentially the same.
Specifically, let $tilde(Y)_(tau, k)$ be the potential outcome at event $k$
corresponding to $bb(1) {event(k) <= tau, status(k) =y}$.
Then the exchangeability condition is that $tilde(Y)_(tau, k) perp treat(j) | history(j-1), event(j), status(j) = a)$ for $0 <= j < k$ and $k = 1, dots, K$.
However,
it has been noted (@RobinsLongitudinal2001) in discrete time that the existence of multiple potential outcomes
can be restrictive and that the resulting exchangeability condition may be too strong. 

== Iterated representation of the target parameter

In this section, we present a simple iterated representation of the observed data target parameter $Psi_tau^"obs" (P)$.
// JOHAN: 
We give an iterated conditional expectations formula for the target parameter in the case with no censoring.
To do so, define
$
    S_k (t | history(k-1)) = product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) Lambda_k^x (dif s | history(k-1))), k = 1, dots, K
$
where $product_(s in (0, t])$ is the product integral over the interval $(0, t]$ (@gill1990survey).
We discuss more thoroughly the implications of this representation in the next section,
where we deal with right-censoring.
// JOHAN: this theorem seems vital, the representation is as such not simple, and would benefit from more motivation/examples
//        also, a reference to Robins iterative regression seems to be missing
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

= Censoring <section:censoring>

In this section, we introduce a right-censoring time $C>0$
at which we stop observing the multivariate jump process
$alpha$.
We aim to establish conditions under which the ICE-IPCW estimator remains consistent for the target parameter.
While the algorithm itself is presented in @alg:ipcwice, we focus here on the assumptions necessary for consistency.
Specifically, let $N^c (t) = bb(1) {C <= t}$ the counting process for the censoring process and
let $T^e$ further denote the (uncensored) terminal event time given by
$
    T^e = inf_(t>0) {N^y (t) + N^d (t) = 1}.
$
// JOHAN: why not allow N^c to jump at the same time? in case of ties we just have to assume that censoring came last!
In the remainder of the paper,
we will assume that the process $N^c$ does not jump at the same time as the processes $N^a, N^ell, N^y, N^d$
with probability 1.

Let $beta(t) = (alpha(t), N^c (t))$ be the fully observable multivariate jump process in $[0, tauend]$.
For technical reasons, we take $Omega = RR times RR^d times N_(bold(X))$ and $cal(F) = cal(B)(RR times RR^d) times.circle cal(N)_(bold(X))$#footnote[This is the so-called canonical setting of @last1995marked.],
where $bold(X)={a, ell, y, d, c} times RR times RR^d$ denotes the mark space and
$cal(N)_(bold(X))$ denotes the $sigma$-algebra $cal(B) ((RR^+ times bold(X))^(K+1))$
 of the full random measure given by
$
    N^beta ((0,t] times {x} times dot times dot) &= bb(1) {x in {a, ell, d, y}} N^alpha ((0, t] times {x} times dot times dot) + bb(1) {x = c} N^c (t) delta_((A(C), L(C))) (dot times dot).
$
//(note that our assumption of no simultaneous jumps of the censoring process and the other processes ensures that
//the right-hand side is a well-defined marked point process).

As before, we let $(event(k), status(k), treat(k), covariate(k))$ be
the event times and marks for the $N^alpha$ process. 
We have in the canonical setting with $beta$
that also #footnote[This follows by considering the sub $sigma$-algebra corresponding to $((event(k),status(k),treat(k),covariate(k)))_(k=1)^K$
    and $P$'s restriction to that sub $sigma$-algebra, because we are then in the canonical setting for $N^alpha$.]
$
    history(k) = sigma(event(k), status(k), treat(k), covariate(k), dots, event(1), status(1), treat(1), covariate(1), treat(0), covariate(0))
$

Then, we observe the trajectories of the process given by $t mapsto N^beta (t and C and T^e)$
and the observed filtration is given by 
$cal(F)_t^tilde(beta) = sigma(beta(s and C and T^e) | s <= t)$. //= cal(F)_(t and C) or cal(G)_(t and T^e),$ 
//where $cal(G)_t = sigma(N^c (s) | s <= t)$ denotes the filtration generated by the censoring process.
//(for a stopping time $T>0$, we use $cal(F)_(t and T)$ to denote stopping time $sigma$-algebra given by the stopping time $t and T$.).
Let $(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k))$ be the observed data given by 
$
    eventcensored(k) &= C and event(k) \
    statuscensored(k) &= cases(status(k) "if" C > event(k), "c" "otherwise") \
    treatcensored(k) &= cases(treat(k)"if" C > event(k), treat(k-1) "otherwise") \
    covariatecensored(k) &= cases(covariate(k) "if" C > event(k), covariate(k-1) "otherwise")
$
for $k = 1, dots, K$.
Importantly, we have that #footnote[The fact that the stopped filtration and the filtration generated by the stopped process are the same is not obvious but follows by Theorem 2.2.14 of @last1995marked.
    Moreover, from this we have $cal(F)^(tilde(beta))_(eventcensored(k)) = cal(F)^(beta)_(event(k) and C and T^e)$ and we may apply Theorem 2.1.14 to the right-hand side of $cal(F)^(beta)_(event(k) and C and T^e)$ to get the desired statement. ].
$
    cal(F)^(tilde(beta))_(eventcensored(k)) = sigma(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k), dots, eventcensored(1), statuscensored(1), treatcensored(1), covariatecensored(1), treat(0), covariate(0)).
$
Abusing notation a bit, we see that for observed histories, we
have $history(k) = historycensored(k)$ if $statuscensored(k) != c$.

Define $cumhazardcensored(k, c, dif t)$ as the cause-specific cumulative hazard (measure) of the $k$'th event and that the event was a censoring event at time $t$ given the observed history $historycensored(k-1)$
and define the corresponding censoring survival function $tilde(S)^c (t | historycensored(k-1)) = prodint(s, event(k-1), t) (1 - cumhazardcensored(k, c, dif s))$.
This determines the probability of being observed at time $t$ given the observed history
up to $historycensored(k-1)$.

Our conditions are similar to those that may be found the literature based on independent censoring (@andersenStatisticalModelsBased1993; Definition III.2.1)
or local independence conditions (@roeysland2024; Definition 4).
Heuristically, one may think of independent censoring in this setting as
$
    &P(event(k) in [t, t + dif t), status(k) = x, treat(k) = m, covariate(k) = l | history(k-1), event(k) >= t) \
        &= P(eventcensored(k) in [t, t + dif t), statuscensored(k) = x, treatcensored(k) = m, covariatecensored(k) = l | historycensored(k-1), eventcensored(k) >= t), qquad x!= c.
$
// Flemming and Harrington; generalization of Theorem 1.3.2.
// to be proven when I feel like it.
for uncensored histories, i.e., when $statuscensored(k-1) != c$
This is essentially the weakest condition such that the observed data martingales
actually identify the unobserved hazards and probabilities.

#theorem[
    Assume that the compensator $Lambda^alpha$ of $N^alpha$ with respect to the filtration $cal(F)^beta_t$ is
    also the compensator with respect to the filtration $cal(F)_t$.
    Then for uncensored histories, we have 
    $
        &bb(1) {statuscensored(n-1) != c} P ((macron(T)_(n), macron(Delta)_(n), A(macron(T)_(n)), L(macron(T)_(n))) in d (t, m, a,l)| historycensored(n-1)) \
            &= bb(1) {macron(T)_(n-1) < t,statuscensored(n-1) != c} (tilde(S) (t- | historycensored(n-1)) sum_(x=a,ell,d,y) delta_x (dif m) psi_(n,x) (t, d(a, l)) cumhazard(n, x, dif t) \
                &qquad + delta_((c, treat(n-1), covariate(n-1))) (dif (m, a, l)) cumhazardcensored(n, c, dif t)) \
    $ <eq:densitycens>
    where $psi_(n,x)$ was defined in @eq:mark
    and $bb(1) {statuscensored(n-1) != c} tilde(S) (t | historycensored(n-1)) = bb(1) {statuscensored(n-1) != c} product_(s in (event(k-1),t]) (1 - sum_(x=a,ell,y,d) cumhazard(n, x, dif s) - cumhazardcensored(n, c, dif s))$.
    
    Further suppose that:
    1. $bb(1) {statuscensored(n-1) != c} tilde(S) (t | historycensored(n-1)) = bb(1) {statuscensored(n-1) != c} tilde(S)^c (t | historycensored(n-1)) S (t | history(n-1))$.
    2. $tilde(S)^c (t | historycensored(n-1)) > eta$ for all $t in (0, tau]$ and $n in {1, dots, K}$ $P$-a.s. for some $eta > 0$.
    // JOHAN: the ICE-IPCW estimator was not defined yet. the following is not an estimator!
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
    Under the independence assumption, by the use of the canonical compensator (@thm:jointdensity (ii)),
    the compensator for $N^alpha$ for $cal(F)_t$ is also the compensator for $tilde(cal(F))^beta_t$.
    Let $M^alpha$ denotes the corresponding martingale decomposition. It follows that
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
    and
    $
        S (t | history(k)) &= product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) cumhazard(k, x, dif s)).
    $
    by it corresponding to the uncensored situation,
    so it follows that we just need to show that
    $
        bb(1) {statuscensored(k) !=c} S^c (t | history(k)) = bb(1) {statuscensored(k) !=c} product_(s in (0, t]) (1 - tilde(Lambda)_k^c (dif s | historycensored(k-1)))
    $
    Because of the independence condition, we have that
    $
        P (eventcensored(k) <= t, statuscensored(k) = c | history(k-1)) = integral_((0,t]) S^c (s- | history(k-1)) Lambda_k^c (dif s | history(k-1))
    $ <eq:densitycens2>
    where 
    $
        S^c (t | history(k-1)) &= product_(s in (0, t]) (1 - Lambda_k^c (dif s | history(k-1)))
    $
    and $Lambda_k^c (dif t | history(k-1))$ is the cause-specific (unobserved) cumulative hazard for the censoring process.
    This must be the same as the observed cause-specific hazard for the censoring process by the previous argument. 
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
    These are explicitly given by the corresponding components in //@eq:canonical.
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

== Algorithm for IPCW Iterative Conditional Expectations Estimator <alg:ipcwice>

// JOHAN: this should be a section for itself not a subsection of = Censoring
In this section, we present an algorithm for the ICE-IPCW estimator based on the preceding discussion.
Two approaches are suggested by @thm:parameter and @thm:ice.
// JOHAN: Theorem 3 is for uncensored data hence it cannot be used so why discuss it? 
However, we do not recommend using the representation in Theorem 3, which involves iterative integration, as this method becomes computationally infeasible even for small values of $K$.

The algorithm for the ICE-IPCW estimator is outlined below.
It requires as inputs the dataset $cal(D)_n$, a time point $tau$ of interest, and a cause-specific cumulative hazard model $cal(L)_h$​ for the censoring process.
This model takes as input the event times, the cause of interest, and covariates from some covariate space $bb(X)$,
// JOHAN: hat(Lambda) should be hat(Lambda^c) correct?
and outputs an estimate of the cumulative cause-specific hazard function $hat(Lambda): (0, tau) times bb(X) -> RR_+$ for the censoring process.

The algorithm also takes a model $cal(L)_o$ for the iterative regressions, which returns a prediction function $hat(nu): bb(X) -> RR_+$ for the pseudo-outcome.
Ideally, both models should be chosen flexibly, since even with full knowledge of the data-generating mechanism, the true functional form of the regression model
cannot typically be derived in closed form.
Also, the model should be chosen such that the predictions are $[0,1]$-valued.

// JOHAN: the algorithm does not seem to adress the probability of treatment weights?
//        how would the algorithm work in uncensored data?
The algorithm can then be stated as follows:

- For each event point $k = K, K-1, dots, 1$ (starting with $k = K$):
    1. Regress $macron(S)_((k)) = eventcensored(k) - eventcensored(k-1)$
       with the censoring as the cause of interest
       on $historycensored(k-1)$ (among the people who are still at risk after $k-1$ events,
       that is $R_k = {i in {1, dots, n} | macron(Delta)_(k,i) in {a, ell}}$)
       using $cal(L)_h$
       to obtain an estimate of the cause-specific cumulative hazard function $hat(Lambda)_k^c$.
    2. Obtain estimates $hat(S)^c (eventcensored(k)- | historycensored(k-1)) = 
    product_(s in (0, macron(T)_(k+1)-macron(T)_(k))) (1 - hat(Lambda)_k^c (s | historycensored(k-1)))$ from step 1.
    3. Calculate the subject-specific pseudo-outcome:
       $
           hat(R)_k = (bb(1) {eventcensored(k) <= tau, statuscensored(k) = y}) / (hat(S)^c (eventcensored(k) - | historycensored(k-1))) \
       $
       Then,
       - If $k < K$:
       
       Let $cal(F)^g_(eventcensored(k))$ denote the history with
       $treat(0) = dots = treatcensored(k) = 1$.
       Then calculate, 
       $
           hat(Z)^a_k = (bb(1) {eventcensored(k) < tau, eventcensored(k) in {a, ell}} hat(nu)_(k) (cal(F)^g_(eventcensored(k)))) / (hat(S)^c (eventcensored(k)- | historycensored(k-1))) + hat(R)_k.
       $
       - If $k = K$, put
       $
           hat(Z)^a_k = hat(R)_k.
       $
    4. Regress $hat(Z)^a_k$ on $history(k-1)$ with model $cal(L)_o$ on the data with $event(k-1) < tau$ and $Delta_k in {a, ell}$ to obtain a prediction function $hat(nu)_(k-1) : cal(H)_(k-1) -> RR^+$.
       Here we denote by $cal(H)_(k-1)$ the set of possible histories of the process up to and including the $k-1$'th event.
       //where $historycensored(k-1) in cal(H)_(k-1)$.
           
- At baseline, we obtain the estimate $hat(Psi)_n = 1/n sum_(i=1)^n hat(nu)_(0) (1, L_i (0))$.

// #algo(
//   title: "ICE-IPCW",
//     parameters: ($cal(D)_n$, $tau$, $cal(L)_o$, $cal(L)_h$ )
// )[
//     $K_tau <- $#smallcaps("getLastEvent")$ (cal(D)_n, tau)$ #comment[get the last non-terminal event number before time $tau$]\
//     for $k <- K_tau$ to $0$: #i\
//     $R_(k) <- {i in {1, dots, n} | macron(Delta)_(k,i) != {y, d, c}}$ #comment[set of subjects with $k$'th event]\
//     $(macron(T)_(k), macron(T)_(k+1), historycensored(k), macron(Delta)_(k+1)) <- cal(D)_(n)[R_(k), (macron(T)_(k), macron(T)_(k+1), historycensored(k), macron(Delta)_(k+1))]$\
//     $I_(k+1) <- macron(T)_(k+1) - macron(T)_(k)$ #comment[interarrival time of the $k$'th event] \
//     $hat(Lambda)_k^c <- cal(L)^c_h (I_(k+1), macron(Delta)_(k+1), historycensored(k)[R_k, ])$ #comment[fit a cause-specific hazard model for the censoring process]\
//     $R_(k) <- {i in R_k | macron(T)_(k,i) < tau}$ #comment[restrict to subjects with $k$'th event before time $tau$] \
//     $(macron(T)_(k+1), macron(Delta)_(k+1), historycensored(k), historycensored(k+1)) <- cal(D)_(n)[R_(k), (macron(T)_(k+1), macron(Delta)_(k+1), historycensored(k), historycensored(k+1))]$ \
//     \
//     #comment[calculate survival function for the censoring process for subjects] \
//     $hat(S)^c_(k+1) <- product_(s in (0, I_(k+1)[R_k,])) (1 - hat(Lambda)_k^c (s | historycensored(k)))$ \
//     \
//     $historycensored(k+1)[, (A(0), dots, A(eventcensored(k+1)))] <- 1$ \
//     $hat(Z)^a_(k+1) <- (bb(1) {macron(T)_(k+1) <= tau, macron(Delta)_(k+1) = y}) / (hat(S)^c_(k+1))$ \
//     if $k < K_tau$: #i\
//     $hat(Z)^a_(k+1) <- hat(Z)^a_(k+1) + (bb(1) {macron(T)_(k+1) < tau, macron(Delta)_(k+1) in {a, ell}} hat(nu)_(k+1) (historycensored(k+1))) / (hat(S)^c_(k+1))$ #comment[calculate the subject-specific pseudo-outcome using $hat(nu)_(k+1)$ to predict] #d\    
//     $hat(nu)_(k) <- cal(L)_o (hat(Z)^a_(k+1),  historycensored(k))$ #comment[regress the pseudo-outcome on the history to obtain a prediction function]\
//     #d\
//     return #$1/n sum_(i=1)^n hat(nu)_(0) (L_i, 1)$ #comment[return the estimate of the target parameter]
// ]

//*Note*: The $Qbar(k)$ have the interpretation of the
//heterogenous causal effect after $k$ events.

= Efficient estimation

In this section, we derive the efficient influence function for $Psi_tau^"obs"$.
The overall objective is to conduct inference for this parameter.
In particular, if $hat(Psi)_n$ is asymptotically linear at $P$ with influence function $phi_tau^* (P)$, i.e.,
$
    hat(Psi)_n - Psi_tau^"obs" (P) = bb(P)_n phi_tau^* (dot; P) + o_P (n^(-1/2))
$
then $hat(Psi)_n$ is regular and (locally) nonparametically efficient (Chapter 25 of @vaart1998).
In this case, one can construct confidence intervals and hypothesis tests based on estimates of the influence function.
Therefore, our goal is to construct an asymptotically linear estimator
of $Psi_tau^"obs"$ with influence function $phi_tau^* (P)$.

The efficient influence function in the nonparametric setting enables the use of machine learning methods to estimate the nuisance parameters,
under certain regularity conditions.
To achieve this, we need to debias our initial ICE-IPCW estimator either through double/debiased machine learning (@chernozhukovDoubleMachineLearning2018) or targeted minimum loss estimation (@laanTargetedMaximumLikelihood2006).
A method for constructing this estimator is presented in @section:onestep.

We derive the efficient influence function using the iterative representation given
in @eq:ipcw, working under the assumptions of @thm:ice.
To proceed, we introduce additional notation and define
$
    Qbar(k) (u  | history(k)) = p_(k a) (u | history(k-1)) + p_(k ell) (u | history(k-1)) + p_(k y) (u | history(k-1)), u < tau.
$ <eq:Qbaru>
This quantity can be estimated using the procedure described in the algorithm in @alg:ipcwice.

A key feature of our approach is that the efficient influence function is expressed in terms of the martingale for the censoring process.
This representation is often computationally simpler, as it avoids the need to estimate multiple martingale terms, unlike the approach of @rytgaardContinuoustimeTargetedMinimum2022.
For a detailed comparison, we refer the reader to the appendix, where we show that our efficient influence function
is the same as the one derived by @rytgaardContinuoustimeTargetedMinimum2022 in the setting with no competing events. 

#theorem("Efficient influence function")[
    The efficient influence function is given by
    #text(size: 7.5pt)[$
        phi_tau^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrt(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1))) bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau}  \
            & times ((macron(Z)^a_(k,tau)- Qbar(k-1)) + integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (Qbar(k-1) (tau  | historycensored(k-1))-Qbar(k-1) (u  | historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u))\
                & +  Qbar(0) - Psi_tau (P),
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
    We compute the efficient influence function by calculating the derivative (Gateaux derivative) of $Psi_tau^"obs" (P_epsilon)$
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
    $mu mapsto product_(u in (s, t]) (1 + mu(u))$ in the direction $h$ is given by (assuming uniformly bounded variation)// it's always finite because; but not necessarily uniformly bounded for all cumhazards; unless we assume that cumhazards themsleves are uniformly bounded.
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
            &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif t_k, dif d_k, dif l_k, dif a_k | historycensored(k-1) = f_(k-1))) \
            &+ integral_(eventcensored(k-1))^(tau) (bb(1) {t_k < tau, d_(k) in {a, ell}})/(tilde(S)^c (t_k - | historycensored(k-1) = f_(k-1)))  ((bb(1) {a_k = 1}) / (densitytrt(t_(k), k)))^(bb(1) {d_(k) = a}) evaluated(partial / (partial epsilon))_(epsilon=0) lr(Qbar(k) (P_epsilon | a_(k), l_(k),t_(k), d_(k), f_(k-1))) \
            &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif t_k, dif d_k, dif l_k, dif a_k | historycensored(k-1) = f_(k-1)) 
    $
    Now note for the second term, we can write
    $
        &integral_(eventcensored(k-1))^(tau) macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) integral_((eventcensored(k-1),t_k)) 1/(1- Delta tilde(Lambda)_k^c (s | historycensored(k-1) = f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
            &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif t_k, dif d_k, dif l_k, dif a_k | historycensored(k-1) = f_(k-1))) \
        &= integral_(eventcensored(k-1))^(tau) integral_(s)^tau macron(Z)^a_(k,tau) (tau, t_k, d_k, l_k, a_k, f_(k-1)) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif t_k, dif d_k, dif l_k, dif a_k | historycensored(k-1) = f_(k-1)) \
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

In this section, we provide a one step estimator for the target parameter $Psi_tau^"obs"$.
For a collection of estimators $eta = ({Lambda_k^x}, {tilde(Lambda)_k^c}, {pi_k}, {nu_(k,tau)}, {tilde(nu)_(k,tau)}, P'_(L(0)) )$,
we consider plug-in estimates of the efficient influence function
$
    phi_tau^* (O; eta) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (pi_j (eventcensored(j), historycensored(j-1))))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) S^(c) (eventcensored(j)- | historycensored(j-1))) bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} \
        & times ((macron(Z)^a_(k,tau) (tilde(S)_(k-1)^(c), nu_(k,tau)) - nu_(k-1,tau)) \
            &qquad+ integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (mu_(k-1)(tau | historycensored(k-1))-mu_(k-1)(u | historycensored(k-1))) 1/(tilde(S)^(c) (u | historycensored(k-1)) S (u- | historycensored(k-1))) (tilde(N)^c (dif u) - tilde(Lambda)_k^c (dif u | historycensored(k-1))) \
        & + nu_(0,tau) (1, L(0)) - Psi_tau^"obs" (eta)
$ <eq:onestep-eif>
where
$
    mu_k (u | historycensored(k)) &= integral_(eventcensored(k))^(u) prodint2(s, eventcensored(k), u) (1-sum_(x=a,l,d,y) Lambda_(k)^x (dif s | historycensored(k))) \
        &quad times [Lambda^y_(k+1) (dif s | historycensored(k)) + bb(1) {s < u} tilde(nu)_(k+1,tau)(1, s, a, history(k)) Lambda^a_(k+1) (dif s | historycensored(k)) + bb(1) {s < u} tilde(nu)_(k+1, tau)(treat(k-1), s, ell, history(k)) Lambda^ell_(k+1) (dif s | historycensored(k))].
$ <eq:mu>

Here, we let $tilde(nu)_(k, tau) (u | f_k)$ be an estimate of $QbarL(k) (u |f_k) := mean(P) [Qbar(k) (u | historycensored(k)) | treatcensored(k) = a_k, statuscensored(k) = d_k, historycensored(k-1) = f_(k-1)]$,
let $nu_(k,tau) (f_k)$ be an estimate of $Qbar(k) (tau | f_k)$, and let $P'_(L(0))$ be an estimate of $P_(L(0))$, the distribution of the covariates at time 0.

We will now describe how to estimate the efficient influence function in practice.
Overall, we consider the same procedure as in @alg:ipcwice with additional steps:
1. Estimate ${nu_(k,tau) (f_k)}$ using the procedure described in @alg:ipcwice.
2. Similarly, estimate ${tilde(nu)_(k,tau) (f_k)}$ using an analogous procedure.
3. Estimate ${Lambda_k^x}$ for $x=a,ell,d,y$ and ${tilde(Lambda)^c_k}$ using step 1 in @alg:ipcwice.
4. Obtain estimates of the propensity score ${pi_k (t, f_(k-1))}$ by regressing
   $treatcensored(k)$ on $(eventcensored(k), historycensored(k-1))$ among
   subjects with $statuscensored(k) = a$ and $statuscensored(k-1) in {a, ell}$ for each $k$.
5. Use the estimates $tilde(nu)_(k,tau) (f_k)$ and the estimates of $Lambda_(k)^x, x=a,ell,d,y$ to numerically compute $mu_(k-1)$
   via @eq:mu.
6. Use the estimated survival functions from step 3 to compute the martingale term in @eq:onestep-eif.
   See also @section:censmg for details on how to approximately compute the censoring martingale term.
7. Substitute the rest of the estimates  into @eq:onestep-eif and obtain the estimate of the efficient influence function.

We note that $Qbar(k) (tau)$ is estimated twice in this procedure.
This redundancy is intentional: it ensures both the computability of the terms involved in the censoring martingale and the availability of updated $nu_(k,tau)$ estimates required for subsequent iterations of the algorithm.
//and the non-martingale terms in @eq:onestep-eif in the following iterations.

Our decision to use  $nu_(k,tau)$ rather than $mu_(k,tau)$ for the non-martingale terms in @eq:onestep-eif is motivated by practical considerations.
In particular, numerical integration may yield less accurate results due to the need to compute $Lambda_k^x$ for $x=a,ell,d,y$ at a dense grid of time points.

In addition, the contribution of the censoring martingale to the efficient influence function is typically small,
and in practice, it can often be ignored without significantly affecting the results.
As such, a simplified procedure that excludes the censoring martingale term or one that computes the censoring martingale term only at a sparse grid of time points may offer substantial computational efficacy
 with minimal bias.
//This simplification leads to slightly conservative standard error estimates.

//For instance, the ICE-IPCW approach would be computationally infeasible along a dense grid of time points.
Now, we turn to the resulting one-step procedure. 
For the ICE-IPCW estimator $hat(Psi)^0_n$, we let $hat(eta) = ({hat(Lambda)^x_k}_(k,x), {hat(Lambda)_k^c}, {hat(pi)_k}_(k), {hat(nu)_(k,tau)}_(k), {tilde(nu)_(k,tau)}_k, bb(P)_n)$
be a given estimator of the nuisance parameters occuring in $phi_tau^* (O; eta)$,
where $bb(P)_n$ denotes the empirical distribution of $L(0)$,
and consider the decomposition
$
    hat(Psi)^0_n - Psi_tau^"obs" (P) &= bb(P)_n phi_tau^* (dot; eta) \
        &-bb(P)_n phi_tau^* (dot; hat(eta)) \
        &+ (bb(P)_n - P) (phi_tau^* (dot; hat(eta)) - phi_tau^* (dot; eta)) \
        &+ R_2 (eta, hat(eta)),
$
where
$
    R_2 (eta, eta') &= P_eta [phi_tau^* (dot; eta')] + Psi^"obs"_tau (eta') - Psi_tau^"obs" (eta)
$
and $Psi_tau^"obs" (hat(eta))  = bb(P)_n [nu_(0, tau) (1, dot)]$.
We consider one-step estimation, that is
$
    hat(Psi)_n &= hat(Psi)^0_n + bb(P)_n phi_tau^* (dot; hat(eta)).
$
This means that to show that
$hat(Psi)_n - Psi_tau^"obs" (P) &= bb(P)_n phi_tau^* (dot; eta) + o_P (n^(-1/2))$,
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
   with $||f||_(L^2_P (O)) = (E_P [f (O)^2])^(1/2)$.

Simple sufficient conditions for this to happen are provided in Lemma ?.
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
        mean(P_0) [phi_(0,tau)^* (O; eta)] + Psi_tau (eta) - Psi_tau (eta_0) =  mean(P_0)[nu_(0) (1,covariate(0)) - Qbar(0) (1,covariate(0))].
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
            &= mean(P_0) [integral_(eventcensored(k - 1))^(tau) bb(1) {eventcensored(k) <= t}(mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1)) ) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)^c_(k) (dif u | historycensored(k-1)) | historycensored(k-1)] \
            &= integral_(eventcensored(k - 1))^(tau) mean(P_0) [bb(1) {eventcensored(k) <= t} | historycensored(k-1)] (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)^c_(k) (dif u | historycensored(k-1))  \
            &=integral_(eventcensored(k - 1))^(tau) (mu_(k-1) (tau | historycensored(k-1)) - mu_(k-1, tau) (u |historycensored(k-1))) (tilde(S)^c_0 (u- | historycensored(k-1)) S_0 (u- | historycensored(k-1)))/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(Lambda)_k^c (d u | historycensored(k-1))
$ <eq:test>
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

    Since we also have for $k >= 1$:
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
so that    
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
#algo(
    title: "censoringMartingale",
    indent-size: 7pt,
      column-gutter: 2pt,
    parameters: ($k$, ${t_1, dots, t_m}$, ${macron(T)_(k,i), macron(T)_(k+1,i)}$, ${cal(F)_(macron(T)_(k,i))}$, ${hat(Lambda)_(k+1)^x}_x$, $tilde(nu)_(k+1)$, ${A(macron(T)_(k,i))}$, ${macron(Delta)_(k+1,i)}$)
)[
    for $i = 1, dots, n$: #i\
    $j_"max" <- max {v | t_v <= tau and macron(T)_(k+1,i) - macron(T)_(k,i)}$ \
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
    $hat(nu)_(tau) (t_j) <- hat(nu)_( tau)^y (t_j) + hat(nu)_(tau)^a (t_j) + hat(nu)_(tau)^ell (t_j) $ #d \
    $hat(M)^c (t_j) <- bb(1) {macron(Delta)_i = c, macron(T)_(k+1,i) - macron(T)_(k,i) <= t_j} - hat(Lambda)_(k+1)^c (t_j | cal(F)_(macron(T)_(k,i)))$ \
    $hat(S)^c (t_j) <- product_(v in (0, t_j]) (1 - hat(Lambda)_(k+1)^c (dif v | cal(F)_(macron(T)_(k,i))))$ \
    $hat("MG")_i <- sum_(j=1)^(k_i) (hat(nu)_(tau) (t_(k_i) | cal(F)_(macron(T)_(k,i))) - hat(nu)_(tau) (t_j | cal(F)_(macron(T)_(k,i))) ) 1/(hat(S)^c (t_j) hat(S)_j ) (hat(M)^c (t_j) - hat(M)^c (t_(j-1)))$ \
    return ${hat("MG")_i}$
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
                        &+ integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (dif a)- Psi_tau (P) 
$

We find immediately that

$
    phi_tau^*(P) &= sum_(k = 1)^(K) product_(j = 0)^(k - 1) ((densitytrtint(event(j), treat(j), j-1)) / (densitytrt(event(j), j-1)))^(bb(1) (status(j) = a)) (bb(1) (status(k-1) in {ell, a}, event(k-1) <= tau))/(exp(- sum_(1 <= j < k) integral_(event(j-1))^(event(j)) hazard(c, s, j-1) dif s)) [ \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (integral_(cal(A)) Qbar(k) (covariate(k-1), a_k, s, a, history(k)) densitytrtint(s, a_k, k) nu_A (dif a_k)) Lambda_k^(a) (d u) \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (mean(P) [Qbar(k) (covariate(k), treat(k-1), event(k), status(k), history(k-1)) | event(k) =s , status(k) = ell, history(k-1)]) Lambda_k^(ell) (d u) \
                &-integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1))) (1) Lambda_k^(y) (d u) -integral_(event(k-1))^(tau and event(k)) 1/(S^c (u | history(k-1)))(0) Lambda_k^(d) (d u) \
                & -integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^bullet (dif u) \
        &+ macron(Z)_(k,tau) (event(k), status(k), covariate(k), treat(k), history(k-1)) + integral_(event(k-1))^tau 1/(S^c (u | history(k-1))) B_(k-1) (u) M_k^c ( d u)] \
                &+ integral Qbar(1) (a, covariate(0)) densitytrtint(0, a, 0) nu_A (dif a)- Psi_tau (P)
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
