#import "template/definitions.typ": *
#import "@preview/colorful-boxes:1.4.3": *
#import "@preview/ctheorems:1.1.3": *
#import "@preview/arkheion:0.1.1": arkheion, arkheion-appendices

#set cite(form: "prose")
#show ref: it => [#text(fill: blue)[#it]]
#show: arkheion.with(
    title: "A Sequential Regression Approach for Efficient Continuous-Time Causal Inference",
    authors: (
        (name: "Johan S. Ohlendorff", email: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen", orcid: "0009-0006-8794-6641"),
        (name: "Anders Munch", email: "a.munch@sund.ku.dk", affiliation: "University of Copenhagen", orcid: "0000-0003-4625-1465"),
        (name: "Thomas A. Gerds", email: "tag@biostat.ku.dk", affiliation: "University of Copenhagen", orcid: "0000-0002-5955-816X"),
    ),
    abstract: [In medical research, causal effects of treatments that may change over
            time on an outcome can be defined in the context of an emulated target
            trial. We are concerned with estimands that are defined as contrasts of
            the absolute risk that an outcome event occurs before a given time
            horizon $tau$ under prespecified treatment regimens. Most of the
            existing estimators based on observational data require a projection
        onto a discretized time scale (@Rose2011). We consider a recently developed continuous-time approach to
        causal inference in this setting (@rytgaardContinuoustimeTargetedMinimum2022), 
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
    keywords: ("continuous-time causal inference", "electronic health records", "survival analysis", "iterative conditional expectations estimator"),
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

= Introduction
Randomized controlled trials (RCTs) are widely regarded as the gold standard for estimating the causal effects of treatments on clinical outcomes.
However, RCTs are often expensive, time-consuming, and in many cases infeasible or unethical to conduct.
As a result, researchers frequently turn to observational data as an alternative.
Even in RCTs, challenges such as treatment noncompliance and time-varying confounding — due to factors like side effects or disease progression — can complicate causal inference.

Marginal structural models (MSMs), introduced by @robins1986, are a widely used approach for estimating causal effects from observational data, particularly in the presence of time-varying confounding and treatment.
Discrete-time MSMs typically require that data be recorded on a discrete time scale.//, capturing all relevant information available to the clinician at each treatment decision point and for the outcome.
Longitudinal Targeted Maximum Likelihood Estimation (LTMLE) (@ltmle) is often used for estimating causal effects in discrete time.

However, many real-world datasets — such as health registries — are collected in continuous time, with patient characteristics updated at irregular, subject-specific times.
These datasets often include detailed, timestamped information on events and biomarkers, such as drug purchases, hospital visits, and laboratory results.
Analyzing data in its native continuous-time form avoids the need for discretization
which can result in bias (@ryalen2019additive @discretization2020guerra @kant2025irregular @sun2023role @adams2020impact @sofrygin2019targeted).

In this paper, we consider a longitudinal continuous-time framework similar to that of @rytgaardContinuoustimeTargetedMinimum2022
and @roysland2011martingale.
Like @rytgaardContinuoustimeTargetedMinimum2022, we define the parameter of interest nonparametrically and focus on estimation and inference through the efficient influence function, yielding nonparametrically locally efficient estimators via a one-step procedure
(@vaart1998 @tsiatis2006semiparametric @bickel1993efficient).

To this end, we propose an inverse probability of censoring iterative conditional expectation (ICE-IPCW) estimator, which, like the iterative regression of @rytgaardContinuoustimeTargetedMinimum2022,
iteratively updates nuisance parameters
by regressing back through the history. Both
methods extend the original discrete-time iterative regression method introduced by @bangandrobins2005.
A key advantage of using iterative regressions is that the resulting estimator will be
less sensitive to/near practical positivity violations
compared to inverse probability of treatment weighting (IPW) estimators.

A key innovation in our method is that these updates are performed by indexing backwards through the number of events rather than through calendar time.
This allows us to apply standard regression techniques to estimate nuisance parameters.
Moreover, our estimator accounts for the temporal complexity of the target parameter through inverse probability of censoring weighting (IPCW).
To draw an analogy, in multi-state settings, state occupation probabilities are expressed as multiple—often numerous—integrals over the transition intensities between states.
In contrast, in non-Markov settings, even if these transition intensities can be estimated, the corresponding integrals are typically not numerically tractable
to compute without resorting to Monte Carlo methods.
The distinction between event-based and time-based updating is illustrated in @fig:timegrid and @fig:eventgrid.
//To the best of our knowledge, no general estimation procedure has yet been proposed for the components involved in the efficient influence function.

For electronic health records (EHRs), the number of registrations for each patient can be enormous.
However, for finely discretized time grids in discrete time,
it has been demonstrated that inverse probability of treatment weighting (IPW)
estimators become increasingly biased and inefficient as the number of time points increases 
whereas iterative regression methods appear to be less sensitive to this issue (@adams2020impact).
Yet, many existing methods for estimating causal effects in continuous time
apply inverse probability of treatment weighting (IPW)
to estimate the target parameter (e.g., @roeysland2024 @roysland2011martingale).

Earlier work on continuous-time methods for causal inference in event history analysis are @roysland2011martingale and @lok2008.
@roysland2011martingale developed identification criteria using a martingale framework based on local independence graphs,
enabling causal effect estimation in continuous time via a change of measure. We shall likewise employ a change of measure to define the target parameter.

Most of the existing literature on continuous-time causal inference have been concerned theoretical identification formulas
In contrast, our work focuses on deriving a feasible, efficient, and debiased estimator.
In this sense, our work is related to @shirakawaContinuousTime; however, they restrict attention to a specific type of nuisance parameter estimator and use a discrete-time approximation of the efficient influence function.
Our method is agnostic to the type of nuisance parameter estimator used and relies on the exact continuous-time efficient influence function.

In @section:setting,
we introduce the setting and notation used throughout the paper.
In @section:estimand, we present the estimand of interest and provide the iterative representation of the target parameter.
In @section:censoring, we introduce right-censoring, discuss the implications for inference, and present the algorithm for estimation.
In @section:efficientinference, we use the Gateaux derivative to find the efficient influence function
and present the debiased ICE-IPCW estimator.
In @section:simulationstudy we present the results of a simulation study
and in  @section:dataapplication we apply the method to electronic health records data from the Danish registers,
emulating a diabetes trial.

#figure(timegrid(new_method: false), caption:  [The figure illustrates the sequential regression approach
    given in @rytgaardContinuoustimeTargetedMinimum2022 for two observations:
    Let $t_1 < dots < t_m$ denotes the event times in the sample.
    Let $P^(G^*)$ denote the interventional probability measure.
    Then, given $mean(P^(G^*))[Y | cal(F)_(t_(r))]$,
    we regress back to $mean(P^(G^*))[Y | cal(F)_(t_(r-1))]$. // (through multiple regressions).
],) <fig:timegrid>

#figure(timegrid(new_method: true), caption: [The figure illustrates the sequential regression approach
    proposed in this article. For each event number $k$ in the sample, we regress back on the history $history(k-1)$.
    Let $P^(G^*)$ denote the interventional probability measure.
    That is, given $mean(P^(G^*))[Y | history(k)]$,
    we regress back to $mean(P^(G^*))[Y | history(k-1)]$.
    The key difference is that we employ $history(k)$ here
    instead of the filtration $cal(F)_(t_(r))$ which turns out to have a simpler representation.
],) <fig:eventgrid>

= Setting and Notation <section:setting>

Let $tauend$ be the end of the observation period.
We will focus on the estimation of the interventional absolute risk in the presence of time-varying confounding at a specified time horizon $tau < tauend$.
We let $(Omega, cal(F), P)$ be a probability space on which all processes
and random variables will be defined.

At baseline,
we record the values of the treatment $treat(0)$ and the time-varying covariates $covariate(0)$
and let $cal(F)_0 = sigma(treat(0), covariate(0))$ be the $sigma$-algebra corresponding
to the baseline information.
We assume that there are a finite number of treatment options.
It is then not a loss of generality to assume that we have two treatment options over time so that $A(t) in {0, 1}$ (e.g., placebo and active treatment),
where $A(t)$ denotes the treatment at time $t>=0$ as contrasts are often of interest.

The time-varying confounders $L(t)$ at time $t>0$ are assumed
to take values in a finite subset $cal(L) subset RR^m$,
so that $L(t) in cal(L)$ for all $t >= 0$.
We assume that the stochastic processes $(L(t))_(t>=0)$ and $(A(t))_(t>=0)$ are càdlàg (right-continuous with left limits),
jump processes.
Furthermore, we require that the times at which the treatment and covariate values may change 
are dictated entirely by the counting processes $(N^a (t))_(t>=0)$ and $(N^ell (t))_(t>=0)$, respectively
in the sense that $Delta A (t) != 0$ only if $Delta N^a (t) != 0$ and $Delta L (t) != 0$ only if $Delta N^ell (t) != 0$ or $Delta N^a (t) != 0$.
The process $N^a$ determines when the doctor may decide on treatment,
but we allow for the time-varying covariates to change at the same time as the treatment values.
$N^ell$ determines when only the covariate values may change, but not the treatment values.
//Note that we allow, for practical reasons, some of the covariate values to change at the same time as the treatment values.
//This can occur if registrations occur only on a daily level if, for example, a patient visits the doctor,
//gets a blood test, and receives a treatment all on the same day.
This means that we can practically assume that $Delta N^a Delta N^ell equiv 0$.
For technical reasons and ease of notation, we shall assume that the number of jumps at time $tauend$
for the processes $L$ and $A$ satisfies $N^a (tauend)+ N^ell (tauend) <= K - 1$ $P$-a.s. for some $K >= 1$.
Let further $(N^y (t))_(t>=0)$ and $(N^d (t))_(t>=0)$
denote the counting processes for the event of interest and the competing event, respectively.
It is reasonable to also assume that $Delta N^y Delta N^x equiv 0$ for $x in {a, ell, d}$ and $Delta N^d Delta N^x equiv 0$ for $x in {a, ell, y}$;
therefore $(N^y, N^d, N^a, N^ell)$ is a multivariate counting process in the sense of @andersenStatisticalModelsBased1993.

Thus, we have observations from a jump process $alpha(t) = (N^a (t), A (t), N^ell (t), L(t), N^y (t), N^d (t))$,
and the natural filtration $(cal(F)_t)_(t>=0)$ is given by $cal(F)_t = sigma (alpha(s) | s <= t) or cal(F)_0$.
Let $event(k)$ be the $k$'th ordered jump time of $alpha$, that is $T_0 = 0$ and $event(k) = inf {t > event(k-1) | alpha (t) != alpha (event(k-1))} in [0, oo]$ be the time of the $k$'th event
and let $status(k) in {c, y, d, a, ell}$ be the status of the $k$'th event, i.e., $status(k) = x$ if $Delta N^x (event(k)) = 1$.
We let $event(k+1) = oo$ if $event(k) = oo$ or $status(k) in {y, d, c}$.
As is common in the point process literature, we define $status(k) = A(oo)= L(oo) = Ø$
if $event(k) = oo$ for the empty mark.

The observed process can without loss of information be encoded as $O= (event(K), status(K), treat(K-1), covariate(K-1), event(K-1), status(K-1), dots, treat(0), covariate(0)) ~ P in cal(M)$ where
$cal(M)$ is the statistical model, i.e., a set of probability measures
and obtain a sample $O = (O_1, dots, O_n)$ of size $n$.
As a concrete example, we refer to @fig:longitudinaldatalong,
which provides the long format of a hypothetical longitudinal dataset
with time-varying covariates and treatment registered at irregular time points,
and its conversion to wide format in @fig:longitudinaldatawide.

To the process $(alpha(t))_(t>=0)$, we associate the corresponding random measure $N$ on $(RR_+ times ({a, ell, y, d, c} times {0,1} times cal(L)))$ by

$
    N (dif (t, x, a, ell)) = sum_(k: event(k) < oo) delta_((event(k), status(k), treat(k), covariate(k))) (dif (t, x, a, ell)),
$ <eq:randommeasure>
where $delta_x$ denotes the Dirac measure on $(RR_+ times ({a, ell, y, d, c} times {0,1} times cal(L)))$.
It follows that the filtration $(cal(F)_t)_(t>=0)$ is the natural filtration of the random measure $N$ (e.g., Theorem 2.5.10 of @last1995marked)
under a no explosion assumption, i.e., that the number of jumps in $[0, tauend]$ is finite $P$-a.s.
Thus, the random measure $N$ carries the same information as the stochastic process $(alpha(t))_(t>=0)$.
This will be critical for dealing with right-censoring.

We work with the natural filtration $(cal(F)_t)_(t>=0)$ generated by the random measure $N$.
within the so-called canonical setting for technical reasons (@last1995marked, Section 2.2).
This is needed to ensure that the compensators can be explicitly written via by the regular conditional distributions of the jump times and marks
but also to ensure that $history(k) = sigma(event(k), status(k), treat(k-1), covariate(k-1)) or history(k-1)$
and $cal(F)_0 = sigma(treat(0), covariate(0))$, where
$history(k)$ stopping time $sigma$-algebra $history(k)$ -- representing the information up to and including the $k$'th event -- associated with
stopping time $event(k)$.

//We let $treat(k)$ ($covariate(k)$) be the treatment (covariate values) at the $k$'th event. //, i.e., $treat(k) = treat(k-1)$ if $status(k) = ell$.
//If $event(k-1) = oo$, $status(k-1) in {y, d, c}$, or $status(k) in {y, d, c}$, we let $treat(k) = Ø$ and $covariate(k) = Ø$.

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
        with $K=2$ for $n=3$. 
        Events are registered at irregular/subject-specific time points
        and are presented in a long format. 
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
        The same example as in @fig:longitudinaldatalong, but presented in a wide data format.
    ])<fig:longitudinaldatawide>

//Intuitively, this means that we assume that $P$ defines only the distribution for the sequence of random variables given by $O$
//and that we work with the natural filtration $(cal(F)_t)_(t>=0)$ generated by the random measure $N^alpha$.
// Formally, we take $Omega = RR times RR^d times N_(bold(X))$ (since $A$ is $bb(R)$-valued and $L$ is $bb(R)^d$-valued) and $cal(F) = cal(B)(RR times RR^d) times.circle cal(N)_(bold(X))$,
// where $bold(X)={a, ell, y, d, c} times RR times RR^d$ denotes the mark space and
// $cal(N)_(bold(X))$ denotes the $sigma$-algebra $cal(B) ((RR^+ times bold(X))^(K))$.
// Here $cal(B) (X)$ denotes the Borel $sigma$-algebra on $X$.

Let $densitytrt(t, k)$ be the probability of being treated at the $k$'th event given $status(k) =a$, $event(k) = t$, $covariate(k)$, and $history(k-1)$.
Let also $cumhazard(k, x, dif t)$ be the cumulative cause-specific hazard measure,
that is the measure given by $bb(1) {t > 0} (P (event(k) in dif t, status(k) = x | history(k-1)))(P(event(k) >= t | history(k-1)))^(-1)$.
At baseline, we let $pi_0 (covariate(0))$ be the probability of being treated given $covariate(0)$
and $mu_0 (dot)$ be the probability measure for the covariate value.

= Estimand of interest and iterative representation <section:estimand>

We are interested in the causal effect of a treatment regime $g$ on the cumulative incidence function of the event of interest $y$ at time $tau$.
We consider regimes which naturally affects the treatment decisions
at each visitation time but not the times at which the patients
visit the doctor. 
The treatment regime $g$ specifies for each event $k = 1, dots, K-1$
with $status(k) = a$ (visitation time) the probability that
a patient receives treatment at the current visitation time via 
$pi_k^* (event(k), history(k-1))$ and at $k=0$ the
initial treatment probability $pi_0^* (covariate(0))$.

Define the likelihood ratio process

$
    W^g (t) &= product_(k=1)^(N_t) ((densitytrtint(event(k), k)^(treat(k)) (1-densitytrtint(event(k), k))^(1-treat(k))) / (densitytrt(event(k), k)^(treat(k)) (1-densitytrt(event(k), k))^(1-treat(k))))^(bb(1) {status(k) = a}) \
        &quad times (pi^*_0 (covariate(0))^(A(0)) (1-pi^*_0 (covariate(0)))^(1-A(0)))/ (pi_0 (covariate(0))^(A(0)) (1-pi_0 (covariate(0)))^(1-A(0))),
$ <eq:weightprocess>
// Should be N_(t-)?

where $N_t = sum_k bb(1) {event(k) <= t}$ is random variable denoting the number of events up to time $t$.
We define the measure $P^(G^*)$ by
$
    (dif P^(G^*))/(dif P) = W^g (tauend), 
$ <eq:likelihoodratio>
which represents the interventional world in which the doctor assigns treatments according to the probability
measure $pi_k^*$ for $𝑘 = 0, dots, 𝐾 − 1$.
Our target parameter is the mean interventional cumulative incidence function at time $tau$ under $P^(G^*)$, which can by identified through the formula
$
    Psi_tau^(g) (P) = mean(P^(G^*)) [N^y (tau)] =  mean(P) [N^y (tau) W^g (tau)],
$ 
where $N^y (t) = sum_(k=1)^K bb(1) {event(k) <= t, status(k) =y}$.
// In order for @eq:likelihoodratio to define
// a likelihood ratio, we need to further assume that $angle.l M^a, M^x angle.r equiv 0$, $x in {ell, y, d}$
// where $angle.l dot, dot angle.r$ denotes the quadratic covariation process (@andersenStatisticalModelsBased1993)
// such that $M^x (t) = N^x (t) - Lambda^x (t)$ is a $P$-$cal(F)_t$ martingale for $x in {a, ell, y, d}$.

In our application, $pi_k^*$ may be chosen arbitrarily,
so that, in principle, _stochastic_, _dynamic_, and _static_ treatment regimes
can be considered. 
However, for simplicity of presentation, we use the static observation plan $pi^*_k = 1$ for all $k = 0, dots, K-1$,
and the methods we present can easily be extended to more complex treatment regimes
and contrasts.
This corresponds to the interventions considered in
@rytgaardContinuoustimeTargetedMinimum2022.
//, albeit we
//work with a specific _version_ of the intervention.

If we do not want to limit ourselves to $K$ events, we can interpret
the target parameter $Psi_tau^(g) (P)$ as
the counterfactual cumulative incidence function of the event of interest $y$ at time $tau$,
when the intervention enforces treatment as part of the $K-1$ first events.
We denote this target parameter by $Psi_tau^(g, K)$ and return to this interpretation later in @section:efficientinference.

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

We now present a simple iterated representation of the target parameter $Psi_tau^g (P)$ in the case with no censoring.
We discuss more thoroughly the implications for inference of this representation, the algorithm for estimation and examples in @section:censoring
where we also deal with right-censoring.
Note that the quantities given in @thm:ice are also defined for $u < tau$
as we need those definitions later for the efficient influence function.

#theorem[
    Let $H_k = (covariate(k), event(k), status(k), treat(k-1), covariate(k-1), event(k-1), status(k-1), dots, treat(0), covariate(0))$ be the history up to and including the $k$'th event,
    but excluding the $k$'th treatment values for $k > 0$. Let $H_0 = covariate(0)$.
    Let $Qbar(K): (u, a_k, h_k) mapsto 0$ and recursively define for $k = K-1, dots, 1$,
    $
        Z^a_(k+1, tau) (u) &= bb(1) {event(k+1) <= u, event(k+1) < tau, status(k+1) = ell) Qbar(k+1) (tau, treat(k), H_(k+1)) \
            &qquad+ bb(1) {event(k+1) <= u, event(k+1) < tau, status(k+1) = a) Qbar(k+1) (tau, 1, H_(k+1)) \
            &qquad + bb(1) {event(k+1) <= u, status(k+1) = y), 
    $ 
    and
    $
        Qbar(k): (u, a_k, h_k) mapsto mean(P) [Z^a_(k+1, tau) (u) | treat(k) = a_k, H_k = h_k], 
    $ <eq:ice>
    for $u <= tau$.
    Then,
    $
        Psi_tau^g (P) = mean(P) [Qbar(0) (tau, 1, covariate(0))].
    $ <eq:ice-end>
    
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
]<thm:ice>

#proof[
    The proof is given in the Appendix (@section:proofice).
] 

Throughout the, we will use the notation $Qbar(k) (u)$ to denote the value of $Qbar(k) (u, treat(k), H_(k))$ and $Qbar(k)$ to denote $Qbar(k) (tau, treat(k), H_(k))$.
$Qbar(k)$ represents the counterfactual probability of the primary event occuring at or before time $tau$
given the history up to and including the $k$'th event, among the people who are at risk of the event before time $tau$ after $k$ events.
@eq:ice then suggests that we can estimate $Qbar(k-1)$ via $Qbar(k)$:
For each individual in the sample, we calculate the integrand in @eq:ice depending on their value of $event(k)$ and $status(k)$,
and apply the intervention by setting $treat(k)$ to 1 if $status(k) = a$.
Then, we regress these values directly on $(treat(k-1), covariate(k-1), event(k-1), status(k-1), dots, treat(0), covariate(0))$
to obtain an estimator of $Qbar(k-1)$.

Note that here, we only set the current value of $treat(k)$ to 1,
instead of replacing all prior values with 1. The latter is certainly closer
to the original iterative conditional expectation estimator (@bangandrobins2005), and mathematically equivalent, but computationally more demanding.
@sofrygin2019targeted demonstrated this in the discrete-time setting.

// e.g., E[ h(X, Y) | Y=1] = E[ h(X, 1) | Y=1]

= Censoring <section:censoring>

In this section, we consider the situation where the observed data is subject to right-censoring.
Let $C>0$ denote the right-censoring time
at which we stop observing the multivariate jump process
$alpha$. Let $N^c$ be the censoring process
given by $N^c (t) = bb(1) {C <= t}$.
In @section:estimand, we proposed an estimation strategy based on fitting a sequence of iterated regressions backword in time for each event.
When the data is subject to right-censoring, standard regression techniques cannot immediately be applied.
To handle this, we use inverse probability of censoring weights. 
Our algorithm is presented in @alg:iceipcw and we later present the assumptions necessary for validity of the ICE-IPCW estimator
in @section:validity.
To do so, we first need additional notation.

In the remainder of the paper,
we will assume that $C != event(k)$ for all $k$ with probability 1.
We now let $(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k))$ for $k=1, dots, K$ be the observed data given by 
$
    eventcensored(k) &= cases(event(k) "if" C > event(k), C "if" C <= event(k) "and" event(k-1) > C, oo "otherwise") \
    statuscensored(k) &= cases(status(k) "if" C > event(k), "c" "if" C <= event(k) "and" statuscensored(k-1) != c, Ø "otherwise") \
    treatcensored(k) &= cases(treat(k)"if" C > event(k), A(C) "if" statuscensored(k-1) = c, Ø "otherwise") \
    covariatecensored(k) &= cases(covariate(k) "if" C > event(k), L(C) "if" statuscensored(k-1) = c, Ø "otherwise")
$ 
for $k = 1, dots, K$,
and $historycensored(k)$ is given by
$
    historycensored(k) = sigma(eventcensored(k), statuscensored(k), treatcensored(k), covariatecensored(k), dots, eventcensored(1), statuscensored(1), treatcensored(1), covariatecensored(1), treat(0), covariate(0)),
$ 
defining the observed history up to and including the $k$'th event.
Thus $tilde(O)=(eventcensored(1), statuscensored(1), treatcensored(1), covariatecensored(1), dots, eventcensored(K), statuscensored(K), treatcensored(K), covariatecensored(K))$ is the observed data
and a sample consists of $tilde(O) = (tilde(O)_1, dots, tilde(O)_n)$ for $n$ independent and identically distributed observations
with $tilde(O)_i tilde P$.
//We will formally show @eq:ftkcens later.

Define $cumhazardcensored(k, c, dif t)$ as the cause-specific hazard measure for censoring of the $k$'th event given the observed history $historycensored(k-1)$,
that is $bb(1) {t > 0} (P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1)))(P(eventcensored(k) >= t | historycensored(k-1)))^(-1)$
and the corresponding conditional censoring survival functions $tilde(S)^c (t | historycensored(k-1)) = prodint(s, event(k-1), t) (1 - cumhazardcensored(k, c, dif s))$,
where $product_(s in (0, t])$ is the product integral over the interval $(0, t]$ (@gill1990survey).
Alost let $tilde(M)^c (t) = tilde(N)^c (t) - tilde(Lambda)^c (t)$ where $tilde(N)^c (t) = bb(1) {C <= t, T^e > t} = sum_(k=1)^K bb(1) {eventcensored(k) <= t, statuscensored(k) = c}$ is the censoring counting process,
$tilde(Lambda)^c (t) = sum_(k=1)^K bb(1) {eventcensored(k-1) < t <= eventcensored(k)} tilde(Lambda)_k^c (t, historycensored(k-1))$ is the censoring compensator
and $S (t | history(k-1)) = product_(s in (0, t]) (1 - sum_(x=a,ell,y,d) Lambda_k^x (dif s, history(k-1)))$
is the overall (uncensored) survival function for the $k$'th event given $history(k-1)$.

With these definitions, we can now present the ICE-IPCW procedure in @alg:iceipcw.
Note that ideally the model for iterative regressions should be chosen flexibly, since even with full knowledge of the data-generating mechanism, the true functional form of the regression model
cannot typically be derived in closed form.
We also recommend that the model should also be chosen such that the predictions are $[0,1]$-valued.

#algorithm("ICE-IPCW procedure")[
    
    Input: Observed data $tilde(O)_i$, $i = 1, dots, n$, estimator of the censoring compensator $hat(Lambda)^c$, time horizon $tau < tauend$,
    and $K-1$.
    
    Output: ICE-IPCW estimator $hat(Psi)_n$ of $Psi_tau^g (P)$.
    
    1. Initialize ($hat(Q)_(K) (tau, a_k, h_k) := 0$).
    2. For each event $k = K - 1, dots, 1$:
       
       a. For each observation, compute $hat(S)^c (eventcensored(k)- | treatcensored(k-1), H_(k-1)) = product_(s in (eventcensored(k-1), eventcensored(k))) (1 - hat(Lambda)^c (s))$.
       
       b. For each observation with $eventcensored(k-1) < tau$ and $statuscensored(k-1) in {a, ell}$ compute the pseudo-outcome $hat(Z)^a_(k,tau)$ as follows:
        - If $statuscensored(k) = y$, calculate $hat(Z)^a_(k,tau) =1 /(hat(S)^c (eventcensored(k)- | treatcensored(k-1), H_(k-1))) bb(1) {eventcensored(k) <= tau}$.
        - Else if $statuscensored(k) = a$, evaluate $hat(Q)_(k+1) (tau, 1, H_(k))$ and calculate
          $
              hat(Z)^a_(k,tau) = 1/ (hat(S)^c (eventcensored(k)- | treatcensored(k-1), H_(k-1))) bb(1) {eventcensored(k) < tau} hat(Q)_(k+1) (tau, 1, H_(k)).
          $
        - Else if $statuscensored(k) = ell$, evaluate $hat(Q)_(k+1) (tau, treatcensored(k-1), H_(k))$,
          and calculate
          $
              hat(Z)^a_(k,tau) = 1/(hat(S)^c (eventcensored(k)- | treatcensored(k-1), H_(k-1))) bb(1) {eventcensored(k) < tau} hat(Q)_(k+1) (tau, treatcensored(k-1), H_(k)).
          $
        c. Regress $hat(Z)^a_(k,tau)$ on $(treatcensored(k-1), macron(H)_(k-1))$
        for the observations with $eventcensored(k-1) < tau$ and $statuscensored(k-1) in {a, ell}$
       to obtain a prediction function $hat(Q)_(k)$.
    3. Compute $hat(Psi)_n = 1/n sum_(i=1)^n hat(Q)_(0) (tau, 1, L_i (0))$.
] <alg:iceipcw>

// We mention how one may obtain an estimator of the censoring
// compensator, but this is a wider topic that we will not concern ourselves with here.
// We provide a model for the censoring
// that can provide estimates of the cause-specific hazard measure $1/(P(eventcensored(k) >= t | treatcensored(k-1), macron(H)_(k-1))) P(eventcensored(k) in dif t, statuscensored(k) = c | treatcensored(k-1), macron(H)_(k-1))$,
// which is always estimable from observed data.
// Then, regress $macron(E)_((k),i) = eventcensoredi(k) - eventcensoredi(k-1)$, known as the $k$'th _interarrival_ time,
//        with the censoring as the cause of interest
// on $(treatcensoredi(k-1), macron(H)_(k-1,i))$ among the patients who are still at risk after $k-1$ events,
// that is for $i$ with $macron(Delta)_(k-1,i) in {a, ell}$ if $k > 1$ and otherwise all $i = 1, dots, n$.
// This gives an estimator of the cause-specific cumulative hazard function $hat(Lambda)_k^c$
// and provides an estimator of the compensator as follows
// $
//     hat(Lambda)_i^c (t) = sum_(k=1)^K bb(1) {eventcensoredi(k-1) < t <= eventcensoredi(k)} hat(Lambda)_k^c (t - eventcensoredi(k-1) | treatcensoredi(k-1), macron(H)_((k-1),i)).
// $

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

== Validity of the ICE-IPCW Estimator <section:validity>
//In this article,
//we do not consider the completed probability space.
//We will interpret $history(k)$ as a random variable instead of a $sigma$-algebra, whenever it is convenient to do so and also make the implicit assumption that whenever we condition on $history(k)$,
//we only consider the cases where $event(k) < oo$ and $status(k) in {a, ell}$.
Let $T^e$ denote the (uncensored) terminal event time, i.e., $T^e = inf_(t>0) {N^y (t) + N^d (t) = 1}$
and let $beta = (alpha, N^c)$ be the full unobserved multivariate jump process in $[0, tauend]$.
//(note that we put $T^e = oo$ if $T^e > tauend$).
Its natural filtration is denoted $cal(F)^"full"_t = sigma(beta(s) | s <= t) or cal(F)_0$.
Thus, we observe the trajectories of the process given by $[0, tauend] in.rev t mapsto beta (t and C and T^e)$
and the observed filtration is given by 
$macron(cal(F))_t = sigma(beta(s and C and T^e) | s <= t) or cal(F)_0$.
//The observed data is then given by @eq:observedata.
//Abusing notation a bit, we see that for observed histories, we
//have $history(k) = historycensored(k)$ if $statuscensored(k) != c$.

We posit an independent censoring condition (1. in @thm:iceipcw) that enables the use of regression techniques similar to those that may be found the literature based on independent censoring (@andersenStatisticalModelsBased1993; Definition III.2.1)
or local independence conditions (@roeysland2024; Definition 4).
//A simple, sufficient condition for this to hold is e.g., that $C perp history(K)$.
Note that 2. is a slight strengthening of the orthogonal martingale condition.
Note that this condition can be relaxed by applying the generalized Trotter formula (@gill1994),
but is not further considered here. 
For example if the compensator of the (observed) censoring
process is absolutely continuous with respect to the Lebesgue measure,
then 2. of @thm:iceipcw is satisfied.
Our third condition in @thm:iceipcw is a positivity condition,
ensuring that the conditional expectations are well-defined.
//2. is mostly a technicality that is generally
//satisfied and not of interest. 

#theorem[
    If
    1. The $P$-$cal(F)_t$-compensator $Lambda$ of $N$ (@eq:randommeasure) is also the $P$-$cal(F)^"full"_t$ compensator of $N$.//, that is $N(t) - Lambda(t)$ is a (local) $P$-$cal(F)^"full"_t$ martingale and a (local) $P$-$cal(F)_t$ martingale.
    2. $Delta tilde(Lambda)_(k)^c (dot, historycensored(k-1)) Delta cumhazard(k, x, dot) equiv 0$ for $x in {a, ell, y, d}$ and $k in {1, dots, K}$.
    3. $tilde(S)^c (t | historycensored(k-1)) > eta$ for all $t in (0, tau]$ and $k in {1, dots, K}$ $P$-a.s. for some $eta > 0$.
    
    Let
    $
        macron(Z)^a_(k, tau) (u) =
        1/(tilde(S)^c (eventcensored(k) - | treatcensored(k-1), macron(H)_(k-1))) &(bb(1) {eventcensored(k) <= u,eventcensored(k) < tau, statuscensored(k) = a}
        Qbar(k) (1, macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, eventcensored(k) < tau, statuscensored(k) = ell} Qbar(k) (treatcensored(k), macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, statuscensored(k) = y})
    $ <eq:pseudooutcomeipcw>
    Then with $h_k = (a_k, l_k, t_k, d_k, dots, a_0, l_0)$,
    $
        bb(1) {d_(1) in {a, ell}, dots, d_(k) in {a, ell}} Qbar(k) (u, a_k, h_k) = mean(P) [macron(Z)^a_(k+1, tau) (u) | treatcensored(k) = a_k, macron(H)_(k) = h_k].
    $ <eq:iceipcw>
    Hence $Psi_tau^g (P)$ is identifiable from the observed data, where i.e., $macron(H)_k = (covariatecensored(k), treatcensored(k-1), eventcensored(k-1), statuscensored(k-1), dots, treat(0), covariate(0))$ is the history up to and including the $k$'th event.
] <thm:iceipcw>

#proof[
    Proof is given in the Appendix (@section:prooficeipcw).
]

= Inference <section:efficientinference>

In this section, we derive the efficient influence function for
$Psi_tau^g$ which we denote by $phi_tau^*$. The effient influence
function is a $P$-indexed function which is square integrable and
has mean zero under $P$. The efficient influence function
$phi_tau^*$ can be interpreted as the functional derivative of
$Psi_tau^g$ (@kennedy_semiparametric_2024 @hines_demystifying_2022).
The efficient influence function can
be used to construct efficient estimators and construct
asymptotically valid tests and confidence interval. In addition,
influence function-based estimators can use of machine learning
methods to estimate the nuisance parameters under certain
regularity. To achieve this, we debias our initial ICE-IPCW
estimator (@alg:onestepsimple and @alg:one-stepgeneral) using double/debiased machine
learning (@chernozhukovDoubleMachineLearning2018). This leads to
the one-step estimator,

$
    hat(Psi)_n = hat(Psi)^0_n + bb(P)_n phi_tau^* (dot; hat(P)),
$

where $hat(Psi)^0_n$ is the initial estimator ICE-IPCW estimator,
and $hat(P)$ is a collection of estimates for the nuisance
parameters appearing in @eq:eif. Under certain regularity
conditions, this estimator is asymptotically linear at $P$ with
influence function $phi_tau^*(dot; P)$.
We derive the efficient influence function using the iterative representation given
in @eq:iceipcw, working under the conclusions of @thm:iceipcw,
by finding the Gateaux derivative of the target parameter.

We also provide an algorithm for the one-step estimator in the uncensored situation
or to obtain conservative inference when censoring is present (@alg:onestepsimple).
Alternatively,
we may use the algorithm in @alg:one-stepgeneral of @section:algorithmgeneral to obtain valid
non-conservative inference although this estimator is not further considered here.
In the rest of this work, we do not consider the estimation
of the censoring martingale further due to the computational difficulties and
leave this as a future research topic.
//However, we do not formally obtain inference if flexible machine learning methods
//are applied to estimate the nuisance parameters.
//If censoring is present, one may not apply flexible machine learning methods
//to estimate censoring nuisance parameters as we have not fully debiased the estimator
//resulting in the possibility of the estimator not being regular.

//Note that this does not constitute a rigorous proof that @eq:eif
//is the efficient influence function, but rather a heuristic argument.

We note the close resemblance of @eq:eif to the well-known efficient influence function
for the discrete time case which was established in @bangandrobins2005,
with the most notable difference being the presence of the martingale term $tilde(M)^c (dif u)$ in @eq:eif.

A key feature of our approach is that the efficient influence function is expressed in terms of the martingale for the censoring process.
This representation is computationally simpler, as it avoids the need to estimate multiple martingale terms.
For a detailed comparison, we refer the reader to the appendix, where we show that our efficient influence function
simplifies to the same as the one derived by @rytgaardContinuoustimeTargetedMinimum2022
(@section:compareif) when the compensators are absolutely continuous with respect to the Lebesgue measure
and under the assumption that $Delta L (t) = 0$ whenever $Delta N^a (t) = 1$.

#theorem("Efficient influence function")[
    Suppose that there is a universal constant $C^* > 0$
    such that $tilde(Lambda)^c_k (tauend, historycensored(k-1); P) <= C^*$ for all $k = 1, dots, K$ and
    every $P in cal(M)$.

    Define
    $
        phi_tau^(*, "discrete") (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1)))   \
            & quad times bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} (macron(Z)^a_(k,tau) (tau)- Qbar(k-1) (tau)) \
            & quad +  Qbar(0) (tau, 1, covariate(0)) - Psi_tau^g (P)
    $ <eq:eifdiscrete>
    and
    $
        phi_tau^(*, "MGc") (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1))) \
            &integral_((eventcensored(k - 1), tau)) bb(1) {s <= eventcensored(k)} (Qbar(k-1) (tau)-Qbar(k-1) (u)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u)
    $ <eq:eifMG>
    The Gateaux derivative of $Psi_tau^g$ at $P in cal(M)$ in the direction of the Dirac measure $delta_(tilde(O))$
    is then given by
    #text(size: 7.5pt)[$
        phi_tau^* (P) &=  phi_tau^(*, "MGc") (P) + phi_tau^(*, "discrete") (P).
    $<eq:eif>]
] <thm:eif>

#proof[The proof is given in the Appendix (@section:proofeif).]

#algorithm("Debiased ICE-IPCW estimator (simple)")[
    Input: Observed data $tilde(O)_i$, $i = 1, dots, n$, time horizon $tau < tauend$,
    and $K-1$.  Estimators of the propensity score $hat(pi)_0$, $hat(pi)_k$ for $k = 1, dots, K-1$
    and the censoring compensator $hat(Lambda)^c$.
    
    Output: One-step estimator $hat(Psi)_n$ of $Psi_tau^g (P)$; estimate of influence function $phi_tau^* (tilde(O); hat(P))$.
    
    1. Compute the ICE-IPCW estimator $hat(Psi)^0_n$ and obtain estimators of $Qbar(k)$ for $k = 0, dots, K-1$
    using @alg:iceipcw.
    
    2. Let $hat(Q)_k$ and $hat(S)^c (dot | historycensored(k-1))$ be the estimates obtained in @alg:iceipcw. Use @eq:eifdiscrete
    based on these estimates and the estimates of $pi_k$ to obtain the estimates $phi^(*, "discrete") (tilde(O)_i; hat(P))$ for $i = 1, dots, n$.
    
    3. Compute the one-step estimator
    $
           hat(Psi)_n = hat(Psi)^0_n + 1/n sum_(i=1)^n phi_tau^(*,"discrete") (tilde(O)_i; hat(P)).
    $
       
    4. Return $hat(Psi)_n$ and $phi_tau^(*,"discrete") (tilde(O_i); hat(P))$ for $i = 1, dots, n$.
] <alg:onestepsimple>


In practice, we may not know the maximum number of events $K_"lim"$ that can occur.
Furthermore, the maximal number of events may be enormous
and it may be difficult to estimate $Qbar(k)$ for large $k$
due to the limited number of observations
with many events.
We show in @thm:adaptive that we can adaptively select $K$ based on the observed data.
For instance, we may pick $K^*=k$ such that $k$ is the largest integer such that
there are at least 40 observations fulfilling that $eventcensored(k-1) < tau$.
Doing so will ensure that we will not have to estimate the terms in @eq:eif
and @eq:iceipcw for which there is very little data. 

#theorem[Adaptive selection of $K$][
    Let $Psi_tau^(g, k^*) (P) = mean(P) [tilde(N)^y (tau) W^g (tau and eventcensored(k^*))]$ for $k^* in bb(N)$
    denote the target parameter when we only intervene up to the $k^*$'th event.
// Anders comment: Is there something missing here? Has the parameter
// Psi_tau^(g, K_(n c)) been defined?
// In general, I find a bit difficult to digest this theorem. How is the estimator \hat\Psi_n defined in relation to k and K_{nc}? 
    Let $N_tau = sum_(k) bb(1) {event(k) <= tau}$
    and $tilde(N)_tau = N_(tau and C)$ be the number of events before time $tau$ in the uncensored and censored data, respectively.
    Let $K_(n c) = max_(v : sum_(i=1)^n bb(1) {tilde(N)_(tau, i) (tau) >= v} > c)$
    denote the maximum number of events with at
    least $c$ people at risk.
    Suppose that we have the decomposition of the
    estimator $hat(Psi)_n$ of $Psi_tau^(g, K_(n c)) (P)$, such that
    $
        hat(Psi)_n - Psi_tau^(g, K_(n c)) (P) = (bb(P)_n - P) phi_tau^(*, K_(n c)) (dot; P) + o_P (n^(-1/2)),
    $
    where $bb(P)_n$ is the empirical measure and $phi_tau^(*, k^*) (dot; P)$ is the efficient influence function for the target parameter $Psi_tau^(g, k^*) (P)$.
    Suppose that there is a number $K_"lim" in bb(N)$, such that $P(N_tau = K_"lim") > 0$,
    but $P(N_(tau) > K_"lim") = 0$ and that $P(tilde(N)_tau = K_"lim") > 0$.
    Then, the estimator $hat(Psi)_n$ satisfies
    $
        hat(Psi)_n - Psi_tau^(g, K_"lim") (P) = (bb(P)_n - P) phi_tau^(*, K_"lim") (dot; P) + o_P (n^(-1/2)).
    $
] <thm:adaptive>

#proof[The proof is given in the Appendix (@section:proofadaptive).]

= Simulation study <section:simulationstudy>

// Anders comment: There are very many results in this section, so I
// think we should move some of them to supplementary material. I
// would argue that the most important point of the simulation is
// comparing to LTMLE. So maybe the censoring setting and some of the
// other estimators could be moved to suppl. We should discuss this
// with Thomas.

We consider a simulation study to evaluate the performance of our ICE-IPCW estimator
and its debiased version. Overall, the purpose of the simulation study is to
establish that our estimating procedure provides valid inference with varying degrees of confounding.

Additionally, the objective is to compare
with existing methods in causal inference, such as
discrete time methods (@ltmle) and a naive
Cox model which treats deviation as censoring,
not addressing time-varying confounding.
In the censored setting, we also address the choice of nuisance parameter models
for the iterative regressions.

*Simulation scenario:*
// Anders comment: I think it would be easier to gain an overview if
// you divide this into two simulations scenarios: First is the one
// without censoring and the other is with censoring. Then you can
// clearly describe the data-generating mechanism, estimator and
// settings completely separately for these two setups. 
We simulate a cohort of patients who initiate treatment at time $t = 0$, denoted by $A(0) = 1$
and who are initially stroke-free, $L(0) = 0$.
All individuals are followed for up to $tauend = 900 "days"$ or until death.
During follow-up, patients may experience (at most) one stroke, stop treatment (irreversibly), die, or drop out 
that is $tilde(N)^x (t) <= 1$ for $x = a, ell, y, c$.
The primary outcome is the _risk of death within $tau = 720$ days_.
We simulate baseline data as $"age" tilde "Unif"(40,90)$,
$L (0) =0$, and $A(0) = 1$.
To simulate the time-varying data, we generate data according to the following compensator
$
    tilde(Lambda) (dif (t, x, a, ell)) &= delta_((y, A(t-), L(t-))) (dif (x, a, ell)) lambda^y (t) dif t \
        &quad + delta_((ell, A(t-), 1)) (dif (x, a, ell)) lambda^ell (t) dif t \
        &quad + delta_((y, L(t-))) (dif (x, ell)) pi_t (dif a) lambda^a (t) dif t \
        &quad + delta_((c, A(t-), L(t-))) (dif (x, a, ell)) lambda_c (t) dif t
$ <eq:simulationintensity>
where
$
    lambda^y (t) &= bb(1) {t <= T^e and C and tauend} lambda^y exp(beta^y_"age" "age" + beta_A^y A(t-) + beta^y_L L(t -)) \
    lambda^ell (t) &= bb(1) {t <= T^e and C and tauend} bb(1) {tilde(N)^ell (t -) = 0} lambda^ell exp(beta^ell_"age" "age" + beta_A^ell A(t-)) \
    lambda^a (t) &= bb(1) {t <= T^e and C and tauend}  bb(1) {tilde(N)^a (t -) = 0} \
        &quad times ((1-bb(1) {tilde(N)^ell (t -) = 0}) gamma_0 exp(gamma_"age" "age") + bb(1) {tilde(N)^ell (t -) = 0} h_z (t; 360; epsilon)) \
    pi_t (dif a) &= bb(1) {t <= T^e and C and tauend}  bb(1) {tilde(N)^a (t -) = 0} (delta_1 (dif a) pi (t | cal(macron(F))_(t-)) + delta_0 (dif a) (1 - pi (t |cal(macron(F))_(t-)))) \
        lambda_c (t) &= bb(1) {t <= T^e and C and tauend} lambda_c
$

where $h_z (t; 360; 5; epsilon)$ is the hazard function for a 
Normal distribution with mean $360$ and standard deviation $5$,
truncated from some small value $epsilon > 0$
and $pi (t | cal(macron(F))_(t-)) = "expit" (alpha_0 + alpha_"age" "age" + alpha_L L(t-))$
is the treatment assignment probability.
Our intervention is $pi^* (t | cal(macron(F))_(t-)) = 1$
which corresponds to sustained treatment throughout the follow-up period
and, in the censored setting, $lambda_c^*=0$.

Note that @eq:simulationintensity states that the intensities
for $N^ell$ and $N^y$ correspond to multiplicative intensity models.
The case $x=a$ requires a bit more explanation:
The visitation intensity depends on whether the patient has had a stroke or not.
If the patient has not had a stroke, the model specifies
that the patient can be expected to visit the doctor
within 360 days (i.e., the patient is scheduled). If the patient has had a stroke, the visitation intensity
is multiplicative, depending on age, and reflects the fact
that a patient, who has had a stroke, is expected to visit the doctor
within the near future.

In the uncensored setting (i.e., $lambda_c = 0$),
we vary the treatment effect on the outcome
corresponding to $beta^y_A >0$, $beta^y_A = 0$, and $beta^y_A < 0$
and the effect of stroke on the outcome $beta^y_L > 0$, $beta^y_L = 0$, and $beta^y_L < 0$.
We also vary the effect of a stroke on the treatment propensity $alpha_(L)$
and the effect of treatment on stroke $beta_(A)^ell > 0$, $beta_(A)^ell = 0$, and $beta_(A)^ell < 0$.
Furthermore, when applying LTMLE,
we discretize time into 8 intervals (see e.g., @sec:discretizing-time).
We consider both the debiased ICE estimator and the ICE estimator
without debiasing.
For modeling of the nuisance parameters,
we select a logistic regression model for the treatment propensity
$pi_k (t, history(k-1))$
and a generalized linear model (GLM) with the option `family = quasibinomial()`
for the conditional counterfactual probabilities $Qbar(k)$.
For the LTMLE procedure, we use an undersmoothed LASSO (@lasso) estimator.
Additionally, we vary sample size in the uncensored setting ($n in {100, 2000, 500, 1000}$);
otherwise $n=1000$.

For the censored setting, we consider a simulation involving _completely_ independent censoring,
where we vary the degree of censoring $lambda_c in {0.0002, 0.0005, 0.0008}$
in @eq:simulationintensity.
We consider only two parameter settings for the censoring martingale
as outlined in @table:simulation-parameters.
Three types of models are considered for the estimation of the counterfactual probabilities $Qbar(k)$:
1. A linear model, which is a simple linear regression of the pseudo-outcomes $hat(Z)_(k,tau)^a$ on the treatment and history variables.
2. An ad-hoc scaled quasibinomial GLM, which is a generalized linear model with the `quasibinomial` as a family argument, where the outcomes are scaled down to $[0, 1]$ by dividing with the largest value of $hat(Z)^a_(k,tau)$ in the sample.
   Afterwards, the predictions are scaled back up to the original scale by multiplying with the largest value of $hat(Z)^a_(k,tau)$ in the sample.
// Anders comment: Why do we need this scaling trick? If the outcome is not restricted to be in [0,1], could we not just use some regression for standard scalar-valued outcomes?
3. A tweedie GLM, which is a generalized linear model with the `tweedie` family, as the pseudo-outcomes $hat(Z)_(k,tau)^a$ may appear marginally as a mixture of a continuous random variable and a point mass at 0.

#set table(
  stroke: (x, y) => if y == 0 {
    (bottom: 0.7pt + black)
  },
  align: (x, y) => (
    if x > 0 { center }
    else { left }
  )
)

#figure(
    table(
        columns: (20%, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto),
        inset: 10pt,
        align: horizon,
        table.vline(x: 1),
        [*Parameters*], [$alpha_(0)$], [$alpha_( "age")$], [$alpha_("L")$], [$beta^y_("age")$], [$beta^ell_("age")$], [$beta^y_(A)$], [$beta^ell_(A)$], [$beta^y_("L")$], [$lambda^y$], [$lambda^ell$], [$gamma_"age"$], [$gamma_0$],
        [*Values \ (varying \ effects)*], [0.3], [0.02], [*-0.2*, \ #underline[0], \ 0.2], [0.025], [0.015], [*-0.3*, \ 0, \ 0.3], [*-0.2*, \ 0, \ 0.2], [-0.5, \ #underline([0]), \ *0.5*], [0.0001], [0.001], [0], [0.005],
        [*Values \ (strong \ confounding)*], [0.3], [0.02], [-0.6, 0.6], [0.025], [0.015], [-0.8, 0.8], [-0.2], [1], [0.0001], [0.001], [0], [0.005],
        [*Values \ (censoring)*], [0.3], [0.02], [-0.6, 0.6], [0.025], [0.015], [-0.8, 0.8], [-0.2], [1], [0.0001], [0.001], [0], [0.005]
    ),
    caption: [
        Simulation parameters for the simulation studies.
        Each value is varied while holding the others fixed.
        Bold values indicate fixed reference values,
        and underlined values denote the scenarios without time-varying confounding.
    ]) <table:simulation-parameters>

== Results
We present the results of the simulation study in @table:no-time-confounding and @table:strong-time-confounding
in the strong and no time confounding cases, respectively.
In the tables, we report the mean squared error (MSE),
mean bias, standard deviation of the estimates, and the mean of the estimated standard error,
as well as coverage of 95% confidence intervals.
We also present boxplots of the results, showing
bias (@fig:boxplot_no_time_confounding, @fig:boxplot_strong_time_confounding, @fig:boxplot_censored, and @fig:boxplot_censored_ice_ipcw),
as well as standard errors (@fig:se_boxplot_no_time_confounding, @fig:se_boxplot_strong_time_confounding, and @fig:boxplot_censored),
depending on the parameters. Additional results, such as those involving sample size, can be found in the appendix (@section:additionalsimresults).

Across all scenarios considered in the uncensored setting (@table:no-time-confounding and @table:strong-time-confounding
and @fig:boxplot_no_time_confounding, @fig:se_boxplot_no_time_confounding, @fig:boxplot_strong_time_confounding, and @fig:se_boxplot_strong_time_confounding),
it appears that the debiased ICE-IPCW estimator has good performance with respect to bias, coverage, and standard errors.
The debiased ICE-IPCW estimator is unbiased even in settings with substantial time-varying confounding and
consistently matches or outperforms both the naive Cox method and the LTMLE estimator.

Interestingly, when strong time-varying 
confounding is present, LTMLE estimates are biased, but the mean squared errors
are about the same as for the debiased ICE-IPCW estimator,
likely owing to the fact that LTMLE has generally smaller standard errors.
This reflects a bias–variance trade-off between continuous-time and discrete-time approaches.
// The standard errors obtained from
// the debiased procedure also appear slightly le biased
// than the standard errors obtained from the LTMLE procedure,
// but this difference may be negligible.
// Note that the choice of nuisance parameter model
// for the iterative regressions is misspecified, so
// we may encounter bias in the standard errors but do
// not see substantial bias in the estimates as the
// method is doubly robust.

In the presence of right-censoring (@fig:boxplot_censored, @fig:se_boxplot_censored, and @fig:boxplot_censored_ice_ipcw),
we see that the debiased ICE-IPCW estimator
remains unbiased across all simulation scenarios
and all choices of nuisance parameter models.
Moreover, standard errors are (slightly) conservative with the trend that
standard errors become more biased as the degree of censoring increases
as is to be expected.

When looking at the selection of nuisance parameter models
for the pseudo-outcomes, we find that the linear model provides the most biased estimates for the non-debiased ICE-IPCW estimator
(@fig:boxplot_censored_ice_ipcw), though the differences are not substantial.
In @fig:boxplot_censored, we see that for the debiased ICE-IPCW estimator,
there is no substantial difference between the linear, scaled quasibinomial, and tweedie models.
Also note that the Tweedie model produces slightly larger standard errors
for the debiased ICE-IPCW estimator
than the linear or scaled quasibinomial models.
However, the differences are otherwise minor.

#let tab = csv("simulation_study/tables/table_no_time_confounding.csv")
#let _ = tab.remove(0)

#figure(
table(
    columns: tab.at(0).len(),
    table.vline(x: 1),
    fill: (_, y) => if ((calc.rem(y, 4) == 0 and y > 0) or (calc.rem(y, 4) == 1)) { gray.lighten(90%) },
    [$beta^y_A$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..tab.slice(0, 4).flatten(),
    table.hline(),
    ..tab.slice(4, 8).flatten(),
    table.hline(),
    ..tab.slice(8, 12).flatten(),
),
    caption: [
        Results for the case without time-varying confounding.
        The coverage, the mean squared error (MSE), average bias,
        standard deviation of the estimates, mean of the estimated standard error
        and the estimator applied are provided. 
    ]
) <table:no-time-confounding>

#let tab = csv("simulation_study/tables/table_strong_time_confounding.csv")
#let _ = tab.remove(0)

#figure(
table(
    columns: tab.at(0).len(),
    table.vline(x: 2),
    fill: (_, y) => if ((calc.rem(y, 4) == 0 and y > 0) or (calc.rem(y, 4) == 1)) { gray.lighten(90%) },
    [$beta^y_A$], [$alpha_L$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..tab.slice(0, 4).flatten(),
    table.hline(),
    ..tab.slice(4, 8).flatten(),
),
    caption: [
        Results for the case with strong time-varying confounding.
        The coverage, the mean squared error (MSE), average bias,
        standard deviation of the estimates, mean of the estimated standard error
        and the estimator applied are provided. 
    ]
) <table:strong-time-confounding>

#figure(
    image("simulation_study/plots/boxplot_no_time_confounding.svg"),
        caption: [
            Boxplots of the estimates for the case without time-varying confounding
            for each estimator in each parameter setting for
            the cases without time confounding.
            The lines indicates the true value of the target parameter $Psi_tau^g (P)$.
        ],
) <fig:boxplot_no_time_confounding>

#figure(
    image("simulation_study/plots/se_boxplot_no_time_confounding.svg"),
    caption: [
            Boxplots of the standard errors for the case without time-varying confounding
            for each estimator (LTMLE and debiased ICE-IPCW) in each parameter setting for
            the cases without time-varying confounding.
            The lines indicates the empirical standard error of the estimates for each estimator.
    ],
) <fig:se_boxplot_no_time_confounding>

#figure(
    image("simulation_study/plots/boxplot_strong_time_confounding.svg"),
    caption: [
        Boxplots of the estimates for the case with strong time-varying confounding
        for each estimator in each parameter setting for
        the cases with strong time-varying confounding.
        The lines indicates the true value of the target parameter $Psi_tau^g (P)$.
    ],
) <fig:boxplot_strong_time_confounding>

#figure(
    image("simulation_study/plots/se_boxplot_strong_time_confounding.svg"),
    caption: [
        Boxplots of the standard errors for the case with strong time-varying confounding
        for each estimator (LTMLE and debiased ICE-IPCW) in each parameter setting for
        the cases with strong time-varying confounding.
        The lines indicates the empirical standard error of the estimates for each estimator.
    ],
) <fig:se_boxplot_strong_time_confounding>

#figure(
    image("simulation_study/plots/boxplot_censored.svg"),
    caption: [
        Boxplots of the estimates for the case with censoring
        for different pseudo-outcome models (linear, scaled quasibinomial, and tweedie)
        with varying degrees of censoring for the debiased ICE-IPCW estimator.
        The lines indicates the true value of the target parameter $Psi_tau^g (P)$.
     ],
) <fig:boxplot_censored>

#figure(
    image("simulation_study/plots/se_boxplot_censored.svg"),
    caption: [
        Boxplots of the standard errors for the case with censoring
        for different pseudo-outcome models (linear, scaled quasibinomial, and tweedie)
        with varying degrees of censoring for the debiased ICE-IPCW estimator.
        The lines indicates the empirical standard error of the estimates.
    ]) <fig:se_boxplot_censored>


#figure(
    image("simulation_study/plots/ice_ipcw_boxplot_censored.svg"),
        caption: [
            Boxplots of the estimates for the case with censoring
            for different pseudo-outcome models (linear, scaled quasibinomial, and tweedie)
            with varying degrees of censoring for the (not debiased) ICE-IPCW estimator.
            The lines indicates the true value of the target parameter $Psi_tau^g (P)$.
        ],
) <fig:boxplot_censored_ice_ipcw>

= Application to Danish Registry Data <section:dataapplication>
To illustrate the applicability of our methods,
we applied them to Danish registry data emulating a target trial in diabetes research.
The dataset consisted of $n=15,937$ patients from the Danish registers who
redeemed a prescription for either DPP-4 (Dipeptidyl peptidase-4)
inhibitors or SGLT2 (sodium/glucose cotransporter 2) inhibitors between 2012 and 2022.
The emulated target trial specifies two regimes for each patient.
One is to start treatment with DPP-4 inhibitors
and do not add or switch to SGLT2 inhibitors during follow-up.
The other with SGLT2 inhibitors is defined analogously.
// Anders comment: Hm, okay, so this is a little bit unclear, because
// that is not what we are estimating when using LTMLE. Are the many
// subject which have more than 20 events within 3.5 years? If not, we
// could say that we are estimating sustained treatment without
// reference to this thing about "the first 20 registrations".
We are interested on the effect of enforcing treatment for the 20 first events/registrations
and the outcome of interest is all-cause mortality
within 1260 days (approximately 3.5 years). For computational reasons,
we enforce treatment for the first 20 events/registrations.

At baseline (time zero), patients were required to have redeemed such a prescription and
to have an HbA1c (hemoglobin A1c) measurement recorded prior to their first prescription redemption.
Additionally, certain exclusion criteria were applied (@emulateempareg).
Within our framework, we defined:
- $N^y$ be the counting process for the event of death.
- $N^c$ the counting process for the event of censoring (e.g., end of study period or emigration).
- $N^a$ the counting process counting drug purchases.
- $N^ell$ the counting process for the measurement dates
  at which the HbA1c was measured.
- $L(t)$ denote the (latest) HbA1c measurement at time $t$ and with the baseline HbA1c measurement at time zero (age, sex, education level, income and duration of diabetes at baseline).
- For each treatment regime (say SGLT2), we defined $A (0) = 1$ if 
  the patient redeemed a prescription for SGLT2 inhibitors first.
  For $t>0$, we defined $A (t) = 1$ if the patient has not purchased DPP-4 inhibitors
  prior to time $t$.

For the nuisance parameter estimation, we used a logistic regression model
for the treatment propensity
the `scaled_quasibinomial` option for the conditional counterfactual probabilities $Qbar(k)$.
Censoring was modeled with a Cox proportional hazards model using only baseline covariates.
As in the simulation study, we omitted the censoring martingale term,
yielding conservative confidence intervals.

A figure of the results is provided in @fig:riskplot_empa.
For comparison, we also applied the Cheap Subsampling confidence interval (@ohlendorff2025cheapsubsamplingbootstrapconfidence)
to see how robust the confidence intervals provided by our procedure are.
The method was considered since bootstrapping the data is computationally expensive.
With 30 bootstrap repetitions and subsample size $m= 12,750$ (approximately 80% of the data),
we found that the Cheap Subsampling confidence intervals
appear very similar to the ones provided by the influence function
across all time horizons.
For the ICE-IPCW estimator (without debiasing),
we see estimates and confidence intervals are very similar
to the ones of the debiased ICE-IPCW estimator.

#figure(
    image("plots/plot_empa.svg"),
        caption: [
            The causal risk of death (upper plot) and risk difference (lower plot) under sustained treatment with SGLT2 inhibitors compared to DPP4 inhibitors
            shown as a function of time since initiation of treatment
            and 95% confidence intervals based on the efficient influence function and Cheap Subsampling confidence intervals ($B = 30, m = 12,750$).
        ],
) <fig:riskplot_empa>

= Discussion

In this article, we have presented a new method for causal inference
in continuous-time settings with competing events and censoring.
We have shown that the ICE-IPCW estimator is consistent for the target parameter,
and provided inference for the target parameter using the efficient influence function.
However, we have not addressed the issue of model misspecification,
which is likely to occur in practice as we have not proposed flexible intensity estimators
for both the censoring intensity and the propensity scores.
There are a few available options for flexible intensity estimation.
For instance, neural networks (see @liguoriModelingEventsInteractions2023 for an overview),
forest based methods (@weissForestBasedPointProcess2013) and gradient boosting
(@ishwaranBoosting).
Other choices include flexible parametric models/highly adaptive LASSO
using piecewise constant intensity models where the likelihood is based on Poisson regression (e.g., @rytgaardContinuoustimeTargetedMinimum2022).
Additionally, future work should thoroughly investigate how
one should model the iterative regressions of the pseudo-outcomes
since they include people observed at different times
and include event times as a regression covariate.
We stress, however, that any regression method may be used.

We could have also opted to use the TMLE framework (@laanTargetedMaximumLikelihood2006) in lieu 
of a one-step estimator. Here, we can use an iterative TMLE procedure
for the $Qbar(k)$'s where we undersmooth the estimation of the censoring compensator
to avoid estimating the censoring martingale term.
This will then yield conservative but valid inference when the censoring distribution is flexibly estimated.

//or a combination of the two TMLE and one-step:
// For instance, one update could be performed, updating $Qbar(k)$
// by solving the an estimation equation corresponding to the empirical mean of the term
// of the efficient influence function that is not the censoring martingale.
// Then, afterwards (if the data is not censored), the semi-TMLE estimates could be debiased
// with the censoring martingale term by adding the empirical mean of the censoring martingale term
// to the estimate.
// This ensures that the efficient score equation
// is solved in one iteration only, while still providing stability
// resulting from not using large inverse probability of treatment weights.

Another potential issue with the estimation of the nuisance parameters is the high dimensionality of the history
and the variables in the history are highly correlated.
//and that the covariates in the history are highly correlated, since many covariates may not change between events.
This may yield issues with regression-based methods. If we adopt a TMLE approach, we may be able to use collaborative TMLE (@van2010collaborative)
to deal with these issues. 

We also did not concern ourselves with the estimation of the compensators here
and the propensity scores.
In this article, we used a simple logistic regression model for the propensity scores.
However, an alternative is to estimate the compensators of the counting processors $N^(a 1)$ and
$N^(a)$, counting the number of times that the doctor has prescribed treatment and
the number of times the patient has visited the doctor, respectively,
and calculating the ratio of the two (estimated) intensities
in the absolutely continuous case.
We only considered the first of these options.
The latter choice, however, makes traditional intensity modeling methods applicable.
Another possibility is to learn the intensities sequentially regressing
the $k$'th event and mark on the history with the $(k-1)$'th event.
We consider this possibility in future work. 

//Another alternative method for inference within the TMLE framework is to use temporal difference learning to avoid iterative estimation of $Qbar(k)$ altogether (@shirakawaLongitudinalTargetedMinimum2024)
//by appropriately extending it to the continuous-time setting;
//however, we can no longer apply just _any_ machine learning method.

//There is also the possibility for functional efficient estimation using the entire interventional cumulative incidence curve
//as our target parameter. There exist some methods for baseline interventions in survival analysis
//(@onesteptmle @westling2024inference).

#bibliography("references/ref.bib",style: "apa")

#show:arkheion-appendices
#set math.equation(numbering: n => {
  numbering("(A.1)", counter(heading).get().first(), n)
})

=

== Proof of @thm:ice <section:proofice>
Let $W_(k, j) = product_(v = k + 1)^(j) ((bb(1) {treat(v) = 1}) / (densitytrt(event(v), v)))^(bb(1) {status(v) = a})$ denote the treatment weights for $k < j$
(taking $densitytrt(event(0), 0) := pi_0 (L(0))$).
We show that 
$
    Qbar(k) (tau, treat(k), H_k) = mean(P) [sum_(j=k+1)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k), H_k]
$ <eq:iterativeProof>
for $k = 0, dots, K - 1$ by backwards induction: 

_Base case_: We consider case $k = K-1$.
First note that 
$
    Z_(K, tau)^a (u) = bb(1) {event(K) <= u, status(K) = y},
$
and
$
    W_(K-1,K) bb(1) {event(K) <= tau, status(K) = y} &= ((bb(1) {treat(K) = 1}) / (densitytrt(event(K), K)))^(bb(1) {status(K) = a}) bb(1) {event(K) <= tau, status(K) = y} \
        &= bb(1) {event(K) <= tau, status(K) = y}
$
so we have
$
    &mean(P) [W_(K-1,K) bb(1) {event(K) <= tau, status(j) = y} | treat(K-1), H_(K-1)] \
        &= mean(P) [bb(1) {event(K) <= tau, status(j) = y} | treat(K-1), H_(K-1)] \
        &= mean(P) [Z_(K, tau)^a (tau) | treat(K-1), H_(K-1)], \
        &= Qbar(K-1) (tau, treat(K-1), H_(K-1).
$
    
_Inductive step_: Assume that the claim holds for $k+1$. Now, we first note that
$
    & bb(1) {event(k+1) < tau, status(k+1) in {a, ell}} \
        &quad times mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k] \
        &= bb(1) {event(k+1) < tau, status(k+1) = a} \
        &#h(1cm) times mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k] \
        &#h(0.5cm) + bb(1) {event(k+1) < tau, status(k+1) = ell} \
        &#h(1cm) times mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k] \
        &= bb(1) {event(k+1) < tau, status(k+1) = a} \
        &#h(1cm) times mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k] \
        &#h(0.5cm) + bb(1) {event(k+1) < tau, status(k+1) = ell} \
        &#h(1cm) times mean(P) [mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k] \
        &=^((a)) bb(1) {event(k+1) < tau, status(k+1) = a} \
        &#h(1cm) times mean(P) [W_(k,k+1) Qbar(k+1) (tau, treat(k+1), H_(k+1)) | event(k+1), status(k+1), treat(k), H_k] \
        &quad + bb(1) {event(k+1) < tau, status(k+1) = ell} \
        &#h(1cm) times mean(P) [Qbar(k+1) (tau, treat(k), H_(k+1)) | event(k+1), status(k+1), treat(k), H_k] 
$ <eq:proofThm1>
In (a), we use the induction hypothesis. Using @eq:proofThm1 then gives, 
$
    &mean(P) [sum_(j=k+1)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k), H_k] \
        &= mean(P) [bb(1) {event(k+1) <= tau, status(k+1) = y} W_(k,k+1)| treat(k), H_k] \
        &quad + mean(P) [sum_(j=k+2)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k), H_k] \
        &=^((b)) mean(P) [bb(1) {event(k+1) <= tau, status(k+1) = y} W_(k,k+1)| treat(k), H_k] \
        &quad + mean(P) [bb(1) {event(k+1) < tau, status(k+1) in {a, ell}} sum_(j=k+2)^K W_(k,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k), H_k] \
        &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} W_(k,k+1) \
            &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) in {a, ell}} \
            &#h(1cm) times mean(P) [W_(k,k+1) mean(P) [sum_(j=k+2)^K W_(k+1,j) bb(1) {event(j) <= tau, status(j) = y} | treat(k+1), H_(k+1)]  | event(k+1), status(k+1), treat(k), H_k] | treat(k), H_k) \
        &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} \
            &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = a} \
            &#h(1cm) times mean(P) [W_(k,k+1) Qbar(k+1) (tau, treat(k+1), H_(k+1)) | event(k+1), status(k+1), treat(k), H_k] \
            &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = ell} \
            &#h(1cm) times mean(P) [Qbar(k+1) (tau, treat(k), H_(k+1)) | event(k+1), status(k+1), treat(k), H_k] | treat(k), H_k) \
        &= mean(P) (bb(1) {event(k+1) <= tau, status(k+1) = y} \
            &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = a} \
            &#h(1cm) times mean(P) [W_(k,k+1) Qbar(k+1) (tau, treat(k+1), H_(k+1)) | covariate(k+1), event(k+1), status(k+1), treat(k), H_k] \
            &#h(0.5cm)+ bb(1) {event(k+1) < tau, status(k+1) = ell} \
            &#h(1cm) times Qbar(k+1) (tau, treat(k), H_(k+1)) | treat(k), H_k).
$ <eq:stepInduction>
Throughout, we use the law of iterated expectations.
In (b), we use that
$
    (event(k) <= tau, status(k) = y) subset.eq (event(j) < tau, status(j) in {a, ell})
$
for all $j = 1, dots, k-1$ and $k = 1, dots, K$ as otherwise the corresponding term would be zero. 
    
The desired statement (@eq:iterativeProof) now follows from the fact that
$
    &mean(P) [W_(k, k+1) Qbar(k+1) (tau, treat(k+1), H_(k+1)) | covariate(k+1), event(k+1), status(k+1) = a, treat(k), H_k] \
        &= mean(P) [(bb(1) {treat(k+1) = 1})/(densitytrtnext(event(k+1), k)) Qbar(k+1) (tau, 1, H_(k+1)) | covariate(k+1), event(k+1), status(k+1) = a, treat(k), H_k] \
        &= mean(P) [(mean(P) [bb(1) {treat(k+1) = 1} | event(k+1), covariate(k+1), status(k+1) =a, treat(k), H_k])/(densitytrtnext(event(k+1), k)) \
            &qquad times Qbar(k+1) (tau, 1, H_(k+1)) | covariate(k+1), event(k+1), status(k+1) = a, treat(k), H_k] \
        &= mean(P) [Qbar(k+1) (tau, 1, H_(k+1)) | covariate(k+1), event(k+1), status(k+1) = a, treat(k), H_k] \
        &= Qbar(k+1) (tau, 1,H_(k+1)),
$ <eq:stepTheorem1>
and @eq:stepInduction.

A similar calculation to @eq:stepTheorem1 shows that $Psi_tau^g (P) = mean(P) [Qbar(0) (tau, 1, covariate(0))]$
and so @eq:ice-end follows.
    
//=

// == Finite dimensional distributions and compensators <appendix:fidi>

// Let $(tilde(X)(t))_(t >= 0)$ be a $d$-dimensional càdlàg jump process,
// where each component $i$ is two-dimensional such that $tilde(X)_i (t) = (N_i (t), X_i (t))$
// and $N_i (t)$ is the counting process for the measurements of
// the $i$'th component $X_i (t)$ such that $Delta X_i (t) != 0$ only if $Delta N_i (t) != 0$
// and $X (t) in cal(X)$ for some Euclidean space $cal(X) subset.eq RR^(m)$.
// Assume that the counting processes $N_i$ with probability 1 have no simultaneous jumps and that the number of event times is bounded by a finite constant $K < oo$.
// Furthermore, let $cal(F)_t = sigma(tilde(X)(s) | s <= t) or sigma(W) in cal(W) subset.eq RR^w$ be the natural filtration.
// Let $T_k$ be the $k$'th jump time of $t mapsto tilde(X) (t)$
// and let a random measure on $RR_+ times cal(X)$
// be given by
// $
//     N (dif (t, x)) = sum_(k : event(k) < oo) delta_((event(k), X(event(k)))) (dif (t, x)).
// $
// Let $cal(F)_(T_((k)))$ be the stopping time $sigma$-algebra associated with
// the $k$'th event time of the process $tilde(X)$.
// Furthermore, let $status(k) = j$ if $Delta N_j (event(k)) != 0$ and let $bb(F)_k = cal(W) times (RR_+ times {1, dots, d} times cal(X))^k$.

// #theorem("Finite-dimensional distributions")[
//     Under the stated conditions of this section:
    
//     (i).  We have $history(k) = sigma( event(k), status(k), X(event(k))) or history(k-1)$
//     and $history(0) = sigma(W)$. Furthermore, $cal(F)^(macron(N))_t = sigma(macron(N) ((0, s], dot) | s <= t) or sigma(W) = cal(F)_t$,
//     where
//     $
//         macron(N) (dif (t, m, x)) = sum_(k:event(k)<oo) delta_((event(k), status(k), X(event(k)))) (dif (t,m,x)).
//     $
//     We refer to $macron(N)$ as the _associated_ random measure. 
    
//     (ii). There exist stochastic kernels $Lambda_(k, i)$ from $bb(F)_(k-1)$ to $RR$ and $zeta_(k,i)$ from $RR_+ times bb(F)_(k-1)$ to $RR_+$ such that the compensator for $N$ is given by,
//     $
//         Lambda (dif (t, m, x)) = sum_(k : event(k) < oo) bb(1) {event(k-1) < t <= event(k)} sum_(i=1)^d delta_i (dif m) zeta_(k,i) (dif x, t, history(k-1)) Lambda_(k,i) (dif t, history(k-1)) product_(l != i) delta_((X_l (event(k-1)))) (dif x_l) 
//     $
//     Here $Lambda_(k, i)$ is the cause-specific hazard measure for $k$'th event of the $i$'th type,
//     and $zeta_(k,i)$ is the conditional distribution of $X_i (event(k))$ given $history(k-1)$, $event(k)$ and $status(k) = i$.

//     // (iii). The distribution of $history(n)$ is given by
//     //    $
//     //       &F_n (d w, d t_1, d delta_1, d x_(11), dots, d x_(1 d), dots, d t_n, d delta_n, d x_(n 1), dots, d x_(n d)) \
//     //         &= (product_(i=1)^n bb(1) {t_(i-1) < t_i} prodint2(u, t_(i-1), t_i) (1-sum_(j=1)^d Lambda_(i,j) (d u, f_(i-1))) sum_(j=1)^d delta_j (d delta_i) zeta_(i,j) (d x_(i j), t_i, f_(i-1)) Lambda_(i,j) (d t_i, f_(i-1))) mu (d w),
//     //    $
//     //    and $f_k = (t_k, d_k, x_k, dots t_1, d_1, x_1, w) in bb(F)_k$ for $n in NN$.
//     //    Here $#scale(160%)[$pi$]$ denotes the product integral.
// ] <thm:jointdensity>
// #proof[
//     To prove (i), we first note that since the number of events are bounded,
//     we have the _minimality_ condition of Theorem 2.5.10 of @last1995marked, so
//     the filtration $cal(F)^N_t = sigma(N ((0, s], dot) | s <= t) or sigma(W) = cal(F)_t$ where
//     $
//         N (dif (t, tilde(x))) = sum_(k : event(k) < oo) delta_((event(k), tilde(X)(event(k)))) (dif (t, tilde(x)))
//     $
//     Thus $history(k) = sigma (event(k), tilde(X)(event(k))) or history(k-1)$
//     and $history(0) = sigma(W)$ in view of Equation (2.2.44) of @last1995marked.
//     To get (i), simply note that since the counting proceses do not jump at the same time,
//     there is a one-to-one corresponding between $status(k)$ and $N^i (event(k))$ for $i = 1, dots, d$,
//     implying that $macron(N)$ generates the same filtration as $N$, i.e., $cal(F)^N_t = cal(F)^(macron(N))_t$ for all $t>=0$.
    
//     To prove (ii), simply use Theorem 4.1.11 of @last1995marked which states that
//     $
//         Lambda(dif (t, m, x)) &= sum_(k: event(k) < oo) bb(1) {event(k-1) < t <= event(k)} (P( (event(k), status(k), X (event(k))) in dif (t, m, x) | history(k-1))) / P(event(k) >= t | history(k-1))  
//     $
//     is a $P$-$cal(F)_t$ martingale.
//     Then, we find by the "no simultaneous jumps" condition, 
//     $
//         P(X(event(k)) in dif x | history(k-1), event(k) = t, status(k) = j) =  P (X_j (event(k)) in dif x_j | history(k-1), event(k) = t, status(k) = j) product_(l != j) delta_((X_l (event(k-1)))) (dif x_l)
//     $
//     We then have,
//     $
//         &P( (event(k), status(k), X (event(k))) in dif (t, m, x) | history(k-1)) / P(event(k) >= t | history(k-1)) \
//             &=sum_(j=1)^d delta_j (dif m) P(X(event(k)) in dif x | history(k-1), event(k) = t, status(k) = j) P(event(k) in dif t, status(k) = j | history(k-1) = f_(k-1)) / P(event(k) >= t | history(k-1) = f_(k-1)).
//     $
//     Letting
//     $
//         zeta_(k,j) (dif x, t, f_(k-1)) := P (X_j (event(k)) in dif x | history(k-1) = f_(k-1), event(k) = t, status(k) = j) \
//         Lambda_(k, j) (dif t, f_(k-1)) := P(event(k) in dif t, status(k) = j | history(k-1) = f_(k-1)) / P(event(k) >= t | history(k-1) = f_(k-1))
//     $
//     completes the proof of (ii).

//     // 3. is simply a straightforward extension of Proposition 1/Theorem 3 of @ryalenPotentialOutcomes
//     // or an application of Theorem 8.1.2 of @last1995marked. It also follows from iterative applications of 2. 
// ]

=

== Proof of @thm:iceipcw <section:prooficeipcw>

We show that if $Qbar(k+1)$ is identified,
then $Qbar(k)$ is identifiable via @eq:pseudooutcomeipcw,
$
    mean(P) [macron(Z)^a_(k+1, tau) (u) | historycensored(k)] &=bb(1) {statuscensored(1) in {a,ell}, dots, statuscensored(k) in {a, ell}} mean(P) [macron(Z)^a_(k+1, tau) (u) | historycensored(k)] + 0 \
        &=^(#text[@lemma:iceone]) bb(1) {statuscensored(1) in {a, ell}, dots, statuscensored(k) in {a, ell}} \
        &quad times {integral_(eventcensored(k))^u (tilde(S) (s- | history(k)))/(tilde(S)^c (s- | history(k)))  mean(P) [Qbar(k+1) (u, 1, macron(H)_(k+1)) | event(k) = s, status(k) = a, history(k)] cumhazardprev(k, a, dif s) \
            &qquad + integral_(eventcensored(k))^u (tilde(S) (s- | history(k)))/(tilde(S)^c (s- | history(k))) mean(P) [Qbar(k+1) (u) | event(k) = s, status(k) = ell, history(k)] cumhazardprev(k, ell, dif s) \
            &qquad + integral_(eventcensored(k))^u (tilde(S) (s- | history(k)))/(tilde(S)^c (s- | history(k)))  cumhazardprev(k, y, dif s) }\
        &=^(#text[@lemma:survivalfactorgeneral]) bb(1) {statuscensored(1) in {a, ell}, dots, statuscensored(k) in {a, ell}} \
        &quad times {integral_(eventcensored(k))^u S (s- | history(k)) mean(P) [Qbar(k+1) (u, 1, macron(H)_(k+1)) | event(k) = s, status(k) = a, history(k)] cumhazardprev(k, a, dif s) \
        &qquad + integral_(eventcensored(k))^u S (s- | history(k)) mean(P) [Qbar(k+1) (u) | event(k) = s, status(k) = ell, history(k)] cumhazardprev(k, ell, dif s) \
            &qquad + integral_(eventcensored(k))^u S (s- | history(k))  cumhazardprev(k, y, dif s) }\
        &=^((*)) bb(1) {statuscensored(1) in {a, ell}, dots, statuscensored(k) in {a, ell}} Qbar(k) (u, history(k)).
$
To obtain $(*)$, we use the definition of $Qbar(k)$ in @eq:ice-end,
writing out the conditional expectation with respect to the densities/cause-specific cumulative hazards. 
This completes the proof.

#lemma[
    Assume condition 1. of @thm:iceipcw.
    $densitycovl(t, dot, k)$ be the probability measure for $covariate(k)$ given $status(k) = ell, event(k) = t$, and $history(k-1)$,
    and $densitycova(t, dot, k)$ be the probability measure for $covariate(k)$ given $status(k) = a, event(k) = t$, and $history(k-1)$.
    Then, we have 
    $
        &bb(1) {statuscensored(k-1) in {a,ell}} P ((eventcensored(k), macron(Delta)_(k), A(eventcensored(k)), L(eventcensored(k))) in dif (t, m, a,l)| historycensored(k-1)) \
            &= bb(1) {eventcensored(k-1) < t,statuscensored(k-1) in {a,ell}} (tilde(S) (t- | historycensored(k-1)) sum_(x=a, ell, d, y) delta_x (dif m) psi_(k,x) (t, dif (a, l)) cumhazard(k, x, dif t) \
                &qquad + delta_((c, A(C), L(C))) (dif (m, a, l)) cumhazardcensored(k, c, dif t)), 
    $ <eq:densitycens>
    where
    $
        psi_(k, x) (t, dif (a, l)) &=   bb(1) {x = a}(delta_(1) (dif a) pi_k (t, l, history(k-1)) \
            &qquad + delta_(0) (dif a) (1 - pi_k (t, l, history(k-1))) densitycova(dif l, t, k)) \
            &+ bb(1) {x = ell} densitycovl(dif l, t, k) delta_(treat(k-1)) (dif a) \
            &+ bb(1) {x in {y, d}} delta_(A(T^e)) (dif a) delta_(L(T^e)) (dif l),
    $ 
    and
    $
        &bb(1) {statuscensored(k-1) != c, eventcensored(k-1) < t} tilde(S) (t | historycensored(k-1)) \
            &= bb(1) {statuscensored(k-1) != c,  eventcensored(k-1) < t} product_(s in (event(k-1),t]) (1 - (sum_(x=a,ell,y,d) cumhazard(k, x, dif s) + cumhazardcensored(k, c, dif s))).
    $
] <lemma:iceone>
#proof[
    A version of the compensator of the random measure $N$ with respect to the filtration $(cal(F)_t)_(t >= 0)$ is by Theorem 4.1.11 (ii) of @last1995marked is
    $
        &Lambda (dif (t, m, a, l)) \
            &= sum_k bb(1) {event(k-1) < t <= event(k)} (P((event(k), status(k), treat(k), covariate(k)) in dif (t, m, a, l) | history(k-1))) / P(event(k) >= t | history(k-1)) \
            &= sum_k bb(1) {event(k-1) < t <= event(k)}  P((covariate(k), treat(k)) in dif (l, a) | history(k-1), event(k) = t, status(k) = m) (P((treat(k), status(k)) in dif (t, m))) / P(event(k) >= t | history(k-1)) \
            &= sum_k bb(1) {event(k-1) < t <= event(k)} sum_(x=a,ell,y,d) P((covariate(k), treat(k)) in dif (l, a) | history(k-1), event(k) = t, status(k) = x) delta_x (dif m) cumhazard(k, x, dif t) \
            &= sum_k bb(1) {event(k-1) < t <= event(k)} sum_(x=a,ell,y,d) psi_(k,x) (t, dif (a, l)) delta_x (dif m) cumhazard(k, x, dif t),
    $
    where we use explicit conditioning and the definition of the cause-specific hazard measures.
    Under condition 1. of @thm:iceipcw, this is also the compensator for $N^alpha$ with respect to the filtration $cal(F)^"full"_t$.
    
    We now let $N^"full" (dif (t, m, a, l)) = N (dif (t, m, a, l)) + delta_((c, A(C), L(C))) (dif (m, a, l)) N^c (dif t)$ be the _full_ random measure,
    where $N^c$ is the counting process for censoring events.
    Similarly, let $tilde(N) (dif (t, m, a, l))$ denote the observed random measure, i.e., the random measure corresponding to the observed data.
    Let $T_((k))^*, Delta_((k))^*,
    A(T_((k))^*), L(T_((k))^*)$ denote the event times and marks of the random measure $N^"full"$.
    Again by Theorem 4.1.11 (ii) of @last1995marked, a version of the compensator of $N^c$ with respect to the filtration $(cal(F)^"full"_t)_(t >= 0)$ is given by
    $
        Lambda^c (dif t) &= sum_k bb(1) {T_((k-1))^* < t <= T_((k))^*} tilde(Lambda)^(c)_k (dif t, cal(F)^"full"_(T_((k-1))^*)),
    $ <eq:compensatorc>
    // Note this must be the same as the compensator with respect to the stopped filtration corresponding to observed data
    // up to the the terminal event
    // On ..., the conditioning sets are the same.
    
    //where $tilde(Lambda)^(c,*)_k (dif t, cal(F)^"full"_(T_((k-1))^*))$ corresponding cause-specific hazard measure. 
    // By the corollary on p. 10 of @protter2005stochastic that the compensator of the stopped process $N^c (t and T^e)$ is
    // $
    //     tilde(Lambda)^c (dif t) = sum_k bb(1) {T_((k-1))^* and T^e < t <= T_((k))^* and T^e} tilde(Lambda)^(c,*)_k (dif t, cal(F)^"full"_(T_((k-1))^*)).
    // $
    // However, this compensator can also by using Theorem 4.1.11 (ii) of @last1995marked as
    // $
    //     sum_k bb(1) {eventcensored(k-1) < t <= eventcensored(k)} cumhazardcensored(k, c, dif t),
    // $
    // noting that a stopped natural filtration is the same as the natural filtration of the stopped process.
    // We conclude by uniqueness of the canonical compensator (Theorem 4.2.2 (ii) of @last1995marked) that
    // $cumhazardcensored(k, c, dif t) = tilde(Lambda)^(c,*)_k (dif t, cal(F)^"full"_(T_((k-1))^*))$ whenever $C > event(k-1)$,
    
    and also that a version of the compensator of $N^"full"$ with respect to the filtration $(cal(F)^"full"_t)_(t >= 0)$ is given by
    $
        Lambda^"full" (dif (t, m, a, l)) = Lambda (dif (t, m, a, l)) + delta_((c, A(C), L(C))) (dif (m, a, l)) Lambda^c (dif t).
    $
    This defines a canonical compensator because each term can be written explicitly as a functional of the history of the process $N^"full"$
    and the baseline covariates. Denote this explicit representation by $rho$, i.e.,
    $
        rho( (L(0), A(0)), N^"full", dif (t, m, a, l)) = Lambda^"full" (dif (t, m, a, l)).
    $
    where $rho$ is now a kernel (in the measure theoretical sense) from ${0, 1} times cal(L) times N_bold(X) times RR_+$ to $RR_+ times bold(X)$.
    Here $N_bold(X)$ denotes the canonical point process space with mark space $bold(X)$ (@last1995marked).
    In this case, $bold(X) = cal(A) times cal(L) times {a, ell, d, y, c}$, where
    $cal(A) = {0, 1}$ and $cal(L) subset.eq RR^d$.
    
    // //K'((L(0), A(0)), N, t, dif (m, a, l)) V' ((A(0),L(0)), N, dif t)
    // for some kernel $K'$ from ${0, 1} times cal(L) times N_bold(X) times RR_+$ to $bold(X)$
    // and some predictable kernel $V'$ from ${0, 1} times cal(L) times N_bold(X) times RR_+$ to $RR_+ times bold(X)$.
    // //This follows since we can pick the kernel $K'$ and $V'$ based on the smaller filtration $cal(F)^alpha_t$.
        
    // Similarly, we find a compensator of the process $N^c$ with respect to the filtration $(cal(F)^"full"_t)_(t>=0)$ given by
    // $
    //     Lambda^c (dif (t, m, a, l)) &=  delta_((c, Ø, Ø)) (dif (m, a, l)) V'' ((A(0),L(0)), N^beta, dif t) 
    // $
    // for some kernel $V''$ from ${0, 1} times cal(L) times N_bold(X) times RR_+$ to $RR_+ times bold(X)$.
    // We now find the _canonical_ compensator of $N^beta (dif (t, m, a, l)) = bb(1) {m in {a, ell, d, y}} N (dif (t, m, a, l)) + delta_((c, Ø, Ø)) (m, a, l)) N^c (dif t)$,
    // given by
    // $
    //     rho ((l_0, a_0), phi^beta, dif (t, m, a, l)) &= bb(1) {m in {a, ell, d, y}} K'((l_(0), a_(0)), phi^alpha, t, dif (m, a, l)) V' ((a_(0),l_(0)), phi^alpha, dif t) \
    //         &+ V' ((a_(0),l_(0)), phi^beta, dif t) delta_((c, Ø, Ø)) (dif (m, a, l)).
    // $
    // //Then $rho ((covariate(0),treat(0)), N^(beta), dif (t, m, a, l))$ is a compensator,
    // //so it is by definition the canonical compensator.
    // By construction,
    // $
    //     &V'' ((treat(0), covariate(0)), (N^(beta))^(event(k-1)), dif t) = tilde(Lambda)_k^c (dif t, cal(F)^"full"_event(k-1)), \ \
    //         &K'((l_(0), a_(0)), (N^(beta))^(event(k-1)), t, dif (m, a, l)) V' ((a_(0),l_(0)), (N^(beta))^(event(k-1)), dif t) = \
    //         &sum_(x=a,ell,d,y) psi_(k,x) (t, d(a,l), history(k-1)) Lambda_k^x (dif t, history(k-1)),
    // $ <eq:compensatorpart>
    // where $(N^("full"))^(event(k-1))$ stopped process at the $(k-1)$'th event time.
    //(see for instance (ii) of @thm:jointdensity to see how we arrive at the second line of @eq:compensatorpart).
    // Do we need to show whether Delta Rho <= 1?

    Note that $T^*_((k+1)) = eventcensored(k+1)$ whenever $event(k) < C$.
    Let $T_(S,1)$ denote the first event time of $N^"full"$ after $T_(S,0):=S$,
    where $S$ is a stopping time with respect to the filtration $(cal(F)^"full"_t)_(t >= 0)$.
    With $S:= T^e and C and event(k)$, we
    have $T_(S, 0) := S = T^e and C and event(k)$. It also holds that
    $T_(S, 0) = eventcensored(k)$ whenever $statuscensored(k-1) in.not {y,d,c}$.
    Using Theorem 4.3.8 of @last1995marked, it therefore holds that
    $
        &bb(1) {statuscensored(1) in.not{c,y,d}, dots, statuscensored(k) in.not {c,y,d}} P( (macron(T)_(k+1), macron(Delta)_(k+1), A(macron(T)_(k+1)), L(macron(T)_(k+1))) in dif (t, m, a,l) | historycensored(k-1)) \
            &=bb(1) {statuscensored(1) in.not{c,y,d}, dots, statuscensored(k) in.not {c,y,d}} P( (T_(S,1)^*, Delta_(S,1)^*, A(T_(S,1)^*), L(T_(S,1)^*)) in dif (t, m, a,l) | historycensored(k-1)) \
            &=^((*)) bb(1) {statuscensored(1) in.not{c,y,d}, dots, statuscensored(k) in.not {c,y,d}} P( (T_(S,1)^*, Delta_(S,1)^*, A(T_(S,1)^*), L(T_(S,1)^*)) in dif (t, m, a,l) | cal(F)^("full")_(T_(S,0))) \
            &=^("Thm. 4.3.8") bb(1) {statuscensored(1) in.not{c,y,d}, dots, statuscensored(k) in.not {c,y,d}} bb(1) {T_(S,0) < t} \
            &quad times product_(s in (T_(S,0), t)) (1 - rho ((L(0),A(0)), (N^("full"))^(T_(S,0)), dif s, {a,y,l,d,y} times {0,1} times cal(L))) rho ((L(0),A(0)), (N^("full"))^(T_(S,0)), dif (t, m, a, l)) \
            &= bb(1) {statuscensored(1) in.not{c,y,d}, dots, statuscensored(k) in.not {c,y,d}} bb(1) {eventcensored(k) < t} \
            &quad times product_(s in (eventcensored(k), t)) (1 - rho ((L(0),A(0)), (N^(tilde(beta)))^(eventcensored(k)), dif s, {a,y,l,d,y} times {0,1} times cal(L))) rho (A(0), L(0), (tilde(N)))^(eventcensored(k)), dif (t, m, a, l)).
    $ <eq:densitycensProof>
    In $(*)$, we use that $cal(F)^("full")_(T_(S,0)) =^((**)) sigma((A(0), L(0)), (N^("full"))^(T_(S,0))) = sigma((A(0), L(0)),(tilde(N))^(eventcensored(k))) =  cal(F)_(eventcensored(k))$ where $(**)$ follows from Theorem 2.1.14 of @last1995marked.
    This is because no terminal event has occurred before or at $T_(S,0)$.
    From @eq:densitycensProof, we get @eq:densitycens by noting that $psi_(k, x) (t, {a,y,l,d,y} times {0,1} times cal(L)) = 1$.
] 

#lemma[
    Assume condition 1. and 2. of @thm:iceipcw.
    Then the left limit of the survival function factorizes on $(0, tau]$, i.e.,
    $
        &bb(1) {statuscensored(k-1)!=c, eventcensored(k-1) < t} tilde(S) (t-| historycensored(k-1)) \
            &= bb(1) {statuscensored(k-1)!=c, eventcensored(k-1) < t}product_(s in (0, t)) (1 - sum_(x=a,ell,y,d) cumhazard(k, x, dif s)) product_(s in (0, t)) (1 - tilde(Lambda)_k^c (dif t, historycensored(k-1)))
    $ 
    for $x=a,ell,y,d$.
] <lemma:survivalfactorgeneral>

#proof[
    // Let $tilde(M)^x = tilde(N)^x - Lambda^x$ (using independent censoring assumption) for $x=a,ell,d,y$ be the
    // martingales of the observed counting processes with respect to the filtration $cal(F)^tilde(beta)_t$,
    // and $tilde(M)^c = tilde(N)^c - tilde(Lambda)^c$ be the martingale of the observed censoring process with respect to the filtration $cal(F)^tilde(beta)_t$.
    // Consider the quadratic covariation process $angle.l dot, dot angle.r$ (@andersenStatisticalModelsBased1993).
    // By (2.4.2) of @andersenStatisticalModelsBased1993, we have
    // //which by the no simultaneous jump condition of the observed censoring process and the observed other processes 
    // $
    //     0=angle.l tilde(M)^c,sum_x tilde(M)^x angle.r_t = integral_0^t Delta tilde(Lambda)_c (s) sum_(x=a,ell,y,d) Lambda^x (dif s).
    // $ <eq:covariationProof>
    // Here $tilde(Lambda)^x$ and $Lambda^x$ are the compensators of the censoring process and the rest of the counting processes, respectively.
    // The latter, up to _indistinguishability_, by independent censoring is,
    // $
    //     tilde(Lambda)_x (dif t) &= sum_(k=1)^K bb(1) {event(k-1) and C < t <= event(k) and C} cumhazard(k, x, dif t), \
    //     tilde(Lambda)_c (dif t) &= sum_(k=1)^K bb(1) {event(k-1) and C < t <= event(k) and C} tilde(Lambda)_c (dif t, historycensored(k-1)).
    // $ <eq:compensatorProofLemma2>
    // Using @eq:covariationProof and @eq:compensatorProofLemma2, we have
    // $
    //     0 &= sum_(k=1)^K bb(1) {event(k-1) and C< t <= event(k) and C} (integral_((event(k-1) and C, t]) Delta cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) cumhazard(k, x, dif s)) \
    //        &qquad + sum_(j=1)^(k-1) integral_((event(j-1) and C, event(j) and C]) Delta tilde(Lambda)^c_j (s, historycensored(j-1)) (sum_(x=a,ell,y,d) cumhazard(k, x, dif s))),
    // $
    // so that $bb(1) {event(k-1) and C < t <= event(k) and C} integral_((event(k-1) and C, t]) Delta cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) cumhazard(k, x, dif s)) = 0$.
    // //since each term is non-negative.
    // Taking the (conditional) expectations on both sides given $historycensored(k-1)$ and using that $Delta cumhazardcensored(k, c, s) != 0$ for only a countable number of $s$'s, we have
    // $
    //     bb(1) {event(k-1) and C < t} tilde(S) (t-| historycensored(k-1)) sum_(eventcensored(k) < s <= t) Delta cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) Delta cumhazard(k, x, s)) &= 0.
    // $ <eq:condProof>
    // //This means that the continuous part of the Lebesgue-Steltjes integral is zero, and thus the integral is evaluated to the sum in @eq:condProof.
    // It follows that for every $t$ with $tilde(S) (t|, cal(F)^tilde(beta)_(macron(T)_k)) > 0$ and $event(k-1) and C < t$, we have
    // $
    //     sum_(eventcensored(k) < s <= t) Delta cumhazardcensored(k, c, s) (sum_(x=a,ell,y,d) Delta cumhazard(k, x, s)) &= 0.
    // $
    //This entails that $Delta tilde(Lambda)_(k+1)^c (t, historycensored(k-1))$ and $sum_x Delta cumhazard(k+1, x, t)$ cannot be both non-zero at the same time.
    To keep notation for the proof brief, let $gamma (v) = Delta tilde(Lambda)_(k)^c (v |historycensored(k-1))$ and $zeta (v) = sum_x Delta cumhazard(k, x, v)$
    and $s = macron(T)_(k-1)$.

    Recall that $tilde(S) (t | historycensored(k-1)) = product_(v in (s, t]) (1 - (sum_(x=a,ell,y,d) cumhazard(k, x, dif v) + tilde(Lambda)_k^c (dif v, historycensored(k-1))))$.
    $
        product_(v in (s, t)) (1 - dif (zeta+gamma) (v)) &= exp(-beta^c) exp( -gamma^c) product_(v in (s, t) \ gamma(v) != gamma(v-) or zeta(v) != zeta(v-))  (1 - Delta ( zeta+gamma)) \
            &=^((*)) exp(-beta^c) exp( -gamma^c) product_(v in (s, t) \ gamma(v) != gamma(v-)) (1- Delta gamma) product_(v in (s, t) \ zeta(v) != zeta(v-)) (1 - Delta zeta) \
            &= product_(v in (s, t)) (1 - dif zeta (v) ) product_(v in (s, t)) (1 - dif gamma (v)),
    $
    where we apply condition 2. of @thm:iceipcw in $(*)$.
    // Then, we have that for $event(k-1) and C < t$
    // $
    //     & bb(1) {product_(v in (s, t)) (1 - dif (zeta+gamma) (v) ) > 0} product_(v in (s, t)) (1 - dif (zeta+gamma) (v)) \
    //         &= bb(1) {product_(v in (s, t)) (1 - dif (zeta+gamma) (v)) > 0} product_(v in (s, t)) (1 - dif zeta (v)) product_(v in (s, t]) (1 - dif gamma (v))
    // $ <eq:condProof2>
    // by splitting the product integral into the continuous and discrete parts,
    // $
    //     product_(v in (s, t)) (1 - dif (zeta+gamma) (v)) &= exp(-beta^c) exp( -gamma^c) product_(v in (s, t) \ gamma(v) != gamma(v-) or zeta(v) != zeta(v-))  (1 - Delta ( zeta+gamma)) \
    //         &=^((*)) exp(-beta^c) exp( -gamma^c) product_(v in (s, t) \ gamma(v) != gamma(v-)) (1- Delta gamma) product_(v in (s, t) \ zeta(v) != zeta(v-)) (1 - Delta zeta) \
    //         &= product_(v in (s, t)) (1 - dif zeta (v) ) product_(v in (s, t)) (1 - dif gamma (v)),
    // $
    // where we apply @eq:nonsimultaneous 
    // under the assumption that $product_(v in (s, t)) (1 - dif (zeta+gamma) (v))>0$. 
    // So we just need to show that $product_(v in (s, t)) (1 - dif (zeta+gamma) (v)) = 0$ if and only if $ product_(v in (s, t)) (1 - dif zeta (v)) = 0$ or $product_(v in (s, t)) (1 - dif gamma (v)) = 0$.
    // Splitting the product integral into the continuous and discrete parts as before, we have
    // $
    //     product_(v in (s, t)) (1 - dif (zeta+gamma) (v)) = 0 <=> exists u in (s, t) "s.t." Delta gamma (u) + Delta zeta (u) = 1 \
    //     product_(v in (s, t)) (1 - dif gamma (v)) product_(v in (s, t)) (1-zeta (v)) = 0 <=> exists u in (s, t) "s.t." Delta gamma (u) = 1 or exists u in (s, t) "s.t." Delta zeta (u) = 1 \
    // $
    // from which the result follows by applying ? and @eq:condProof2, since this shows that
    // $
    //     &bb(1) {product_(v in (s, t)) (1 - dif (zeta+gamma) (v)) > 0} product_(v in (s, t)) (1 - dif zeta (v)) product_(v in (s, t]) (1 - dif gamma (v)) \
    //     &=bb(1) {product_(v in (s, t)) (1 - dif zeta (v)) > 0 or product_(v in (s, t)) (1 - dif gamma (v)) > 0} product_(v in (s, t)) (1 - dif zeta (v)) product_(v in (s, t]) (1 - dif gamma (v)) \
    //         &=product_(v in (s, t)) (1 - dif zeta (v)) product_(v in (s, t]) (1 - dif gamma (v)),
    // $
    // for $event(k-1) and C < t$.
    //(*NOTE*: We already the seen implication of the first part to the second part since $Delta gamma (u) + Delta zeta (u) <= 1$; otherwise the survival function given in @thm:iceipcw would not be well-defined.)
]

=

== Comparison with the EIF in @rytgaardContinuoustimeTargetedMinimum2022 <section:compareif>
Let us define in the censored setting
$
    W^g (t) = product_(k = 1)^(tilde(N)_t) (bb(1) {treatcensored(k) = 1}) / (pi_k (eventcensored(k), historycensored(k-1))) product_(k=1)^(tilde(N)_t) (bb(1) {status(k) != c}) / (product_(u in (eventcensored(k-1), eventcensored(k))) (1 - cumhazardcensored(k,c,dif u))),
$
in alignment with @eq:weightprocess
with perfect compliance at time zero. 
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
Here, $tilde(M)^x$ denotes the observed martingales with respect to the observed filtration.
We note, for instance, for $x= ell$ that
$
    &mean(P^(G^*)) [N_y (tau) | Delta N^x (t) = 1, cal(F)_(t-)] \
        &=sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)}mean(P^(G^*)) [N_y (tau) | event(k) = t, status(k) = x, history(k-1)] \
        &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} lim_(epsilon -> 0) mean(P^(G^*)) [N_y (tau) | event(k) in (t, t+epsilon), status(k) = x, history(k-1)] \
        &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} lim_(epsilon -> 0) (mean(P^(G^*)) [N_y (tau) bb(1) { event(k) in (t, t+epsilon), status(k) = x} | history(k-1)]) / (mean(P^(G^*)) [bb(1) { event(k) in (t, t+epsilon), status(k) = x} | history(k-1)]) \
        &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} \
        &qquad lim_(epsilon -> 0) (mean(P^(G^*)) [mean(P^(G^*)) [Qbar(k) (tau) | event(k), status(k) = x, history(k-1)] bb(1) {event(k) < tau} bb(1) { event(k) in (t, t+epsilon), status(k) = x} | history(k-1)]) / (mean(P^(G^*)) [bb(1) { event(k) in (t, t+epsilon), status(k) = x} | history(k-1)]) \
        &=^(*) sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} (mean(P) [Qbar(k) (tau) | event(k) =t, status(k) = x, history(k-1)] S (t| history(k-1)) lambda^x_k (t , history(k-1))) /(S (t| history(k-1)) lambda^x_k (t , history(k-1))) \
        &= sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} mean(P) [Qbar(k) (tau) | event(k) =t, status(k) = x, history(k-1)],
$ <eq:rytgaardproof1>
where we, in $(*)$, apply dominated convergence.
Similarly, we may find that
$
    mean(P^(G^*)) [N_y (tau) | Delta N^y (t) = 1, cal(F)_(t-)] = 1, \
    mean(P^(G^*)) [N_y (tau) | Delta N^d (t) = 1, cal(F)_(t-)] = 0, \
    mean(P^(G^*)) [N_y (tau) | Delta N^a (t) = 1, cal(F)_(t-)] = sum_(k=1)^K bb(1) {event(k-1) < t <= event(k)} Qbar(k) (tau, 1, H_(k)).
$ <eq:rytgaardproof2>
For the first term in @eq:rytgaardeif, we find that
$
    &mean(P^(G^*)) [N_y (tau) | L(t), N^ell (t), cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | N^ell (t), cal(F)_(t-)] \
        &= mean(P^(G^*)) [N_y (tau) | L(t), Delta N^ell (t) = 0, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 0, cal(F)_(t-)] \
        &quad +mean(P^(G^*)) [N_y (tau) | L(t), Delta N^ell (t) = 1, cal(F)_(t-)] - mean(P^(G^*)) [N_y (tau) | Delta N^ell (t) = 1, cal(F)_(t-)] \
        &= 0 \
        &quad + sum_(k=1)^(K-1) bb(1) {event(k-1) < t <= event(k)} (mean(P^(G^*)) [N_y (tau) | L(event(k)), event(k) = t, status(k) = ell, history(k-1)]-mean(P^(G^*)) [N_y (tau) | event(k) = t, status(k) = ell, history(k-1)]) \
        &= sum_(k=1)^(K-1) bb(1) {event(k-1) < t <= event(k)} bb(1) {event(k) < tau, status(k) = ell}  (Qbar(k) (tau) - mean(P) [Qbar(k) (tau) | event(k) = t , status(k) = ell, history(k-1)]).
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
    phi_tau^*(P) &=sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1))) bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} \
        &[integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) (Qbar(k) (tau, 1, u, a, historycensored(k-1))- B_(k-1) (u)) tilde(M)^(a) (d u) \
            &quad+integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) (mean(P) [Qbar(k) (tau) | event(k) =u , status(k) = ell, history(k-1)] - B_(k-1) (u)) tilde(M)^(ell) (d u) \
            &quad+integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) (1 - B_(k-1) (u)) tilde(M)^(y) (d u) +integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)))(0 - B_(k-1) (u)) tilde(M)^(d) (d u) \
            &quad+  1/(tilde(S)^c (eventcensored(k) | historycensored(k-1))) bb(1) (eventcensored(k) < tau, statuscensored(k) = ell, k < K) ( Qbar(k) (tau) - mean(P) [Qbar(k) (tau) | eventcensored(k), status(k) = ell, history(k-1)] )]\
        &+ Qbar(0) (tau, 1, covariate(0))- Psi_tau^g (P) \
        &= sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1))) bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} [ \
            &quad-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) Qbar(k) (1, covariatecensored(k-1), u, a, historycensored(k-1))  lambda^a_k (u , historycensored(k-1)) dif u \
            &quad-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) mean(P) [Qbar(k) (tau) | eventcensored(k) =s , status(k) = ell, historycensored(k-1)] lambda_k^(ell) (u , historycensored(k-1)) dif u \
            &quad-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) (1) lambda_k^(y) (u , historycensored(k-1)) dif u -integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)))(0) lambda_k^(d) (u , historycensored(k-1)) dif u \
            &quad -integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) B_(k-1) (u) M^bullet (dif u) + macron(Z)^a_(k,tau) (tau) + integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1))) B_(k-1) (u) tilde(M)^c ( d u)] \
        &+ Qbar(0) (tau, 1, covariate(0)) - Psi_tau^g (P),
$ <eq:rytgaard55>
where $M^bullet (t) = sum_(x=a,ell,d,y,c) tilde(M)^x (t)$ and $lambda_k^bullet (s , historycensored(k-1)) = sum_(x=a,ell,d,y,c) lambda^x_k (s , historycensored(k-1))$.
Now note that 
$
    & integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (Qbar(k-1)(tau) - Qbar(k-1)(u)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) M^bullet (dif u) \
        &=(Qbar(k-1)(tau) - Qbar(k-1)(eventcensored(k))) 1/(tilde(S)^c (eventcensored(k) | historycensored(k-1)) S (eventcensored(k) | historycensored(k-1))) bb(1){eventcensored(k) <= tau} \
        &quad-Qbar(k-1)(tau) integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda_k^bullet (u , historycensored(k-1)) dif u \
        &quad+ integral_(eventcensored(k-1))^(tau and eventcensored(k)) (Qbar(k-1)(u))/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda_k^bullet (u , historycensored(k-1)) dif u.
$ <eq:rytgaard5>
Let us calculate the first integral of @eq:rytgaard5. We have,
$
    & Qbar(k-1)(tau) integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u | historycensored(k-1))) lambda_k^bullet (u , historycensored(k-1)) dif u  \
        &= Qbar(k-1)(tau) (1/(tilde(S)^c (eventcensored(k) and tau | historycensored(k-1)) S (eventcensored(k) and tau | historycensored(k-1)))-1),
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
        &=^((*)) 1/(tilde(S)^c (tau and eventcensored(k) | historycensored(k-1)) S (tau and eventcensored(k) | historycensored(k-1))) Qbar(k-1) (tau and eventcensored(k)) \
        &-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/ (tilde(S)^c (s | historycensored(k-1)))  [  Qbar(k) (1, covariate(k-1), s, a, historycensored(k-1)) lambda_k^a (s , historycensored(k-1))  \
            &quad quad +  mean(P) [Qbar(k) (tau) | event(k) =s , status(k) = ell, history(k-1)] lambda_k^ell (s , historycensored(k-1))  \
            &quad quad +  lambda_k^y (s , historycensored(k-1)) ] dif s.
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
        &quad times 1/(tilde(S)^c (tau and eventcensored(k) | historycensored(k-1)) S (tau and eventcensored(k) | historycensored(k-1))) Qbar(k-1) (tau and eventcensored(k)) \
        &-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/ (tilde(S)^c (s | historycensored(k-1)))  [  Qbar(k) (1, covariate(k-1), s, a, historycensored(k-1)) lambda_k^a (s , historycensored(k-1))  \
            &quad quad +  mean(P) [Qbar(k) (tau) | event(k) =s , status(k) = ell, history(k-1)] lambda_k^ell (s , historycensored(k-1))  \
            &quad quad +  lambda_k^y (s , historycensored(k-1)) ] dif s \
        &=-integral_(eventcensored(k-1))^(tau and eventcensored(k)) 1/ (tilde(S)^c (s | historycensored(k-1)))  [  Qbar(k) (1, covariate(k-1), s, a, historycensored(k-1)) lambda_k^a (s , historycensored(k-1))  \
            &quad quad +  mean(P) [Qbar(k) (tau) | event(k) =s , status(k) = ell, history(k-1)] lambda_k^ell (s , historycensored(k-1))  \
            &quad quad +  lambda_k^y (s , historycensored(k-1)) ] dif s  +Qbar(k-1)(tau).
$
This now shows that @eq:rytgaard55 is equal to @eq:eif.

=

== Proof of @thm:eif <section:proofeif>
We let $Qbar(k) (u, a_k, h_k; P)$ denote the right-hand side of @eq:iceipcw,
with $P$ being explicit in the notation and likewise define the notation with $macron(Z)^a_(k, tau) (u; P)$.
We compute the efficient influence function by calculating the derivative (Gateaux derivative) of $Psi_tau^g (P_epsilon)$
with $P_epsilon = P + epsilon (delta_(O)-P)$ at $epsilon = 0$,
where $delta$ denotes the Dirac measure at the point $O$.
First note that
$
    evaluated(partial / (partial epsilon))_(epsilon=0) Psi_tau (P_epsilon) = Qbar(0) (tau) - Psi_tau^g (P) + integral evaluated(partial / (partial epsilon))_(epsilon=0) Qbar(0) (tau, 1, l; P_epsilon) P_L (dif l).
$ <eq:baselineeif>
    
Then note that
$
    &evaluated(partial / (partial epsilon))_(epsilon=0) Lambda_(k, epsilon)^c (dif t | f_(k-1)) \
        &=evaluated(partial / (partial epsilon))_(epsilon=0) (P_epsilon (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P_epsilon (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) \
        &=evaluated(partial / (partial epsilon))_(epsilon=0) (P_epsilon (eventcensored(k) in dif t, statuscensored(k) = c, historycensored(k-1) = f_(k-1))) / (P_epsilon (eventcensored(k) >= t, historycensored(k-1) = f_(k-1))) \
        &= (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) (bb(1) {eventcensored(k) in dif t, statuscensored(k) = c}-P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) \
        &quad- (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) (bb(1) {eventcensored(k) >= t} - P(eventcensored(k) >= t | historycensored(k-1) = f_(k-1)))(P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P (eventcensored(k) >= t| historycensored(k-1) = f_(k-1)))^2 \
        &= (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) (bb(1) {eventcensored(k) in dif t, statuscensored(k) = c}) / (P (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) - bb(1) {eventcensored(k) >= t} (P (eventcensored(k) in dif t, statuscensored(k) = c | historycensored(k-1) = f_(k-1))) / (P (eventcensored(k) >= t| historycensored(k-1) = f_(k-1)))^2 \
        &= (delta_(historycensored(k-1)) (f_(k-1)))/P(historycensored(k-1) = f_(k-1)) 1/(P (eventcensored(k) >= t | historycensored(k-1) = f_(k-1))) (bb(1) {eventcensored(k) in dif t, statuscensored(k) = c} - bb(1) {eventcensored(k) >= t} tilde(Lambda)^c_k (dif t | historycensored(k-1) = f_(k-1))),
$
so that
$
    &evaluated(partial / (partial epsilon))_(epsilon=0) product_(u in (s, t)) (1- tilde(Lambda)_(k,epsilon)^c (dif t | f_(k-1))) \
        &=evaluated(partial / (partial epsilon))_(epsilon=0) 1/(1-Delta tilde(Lambda)_(k,epsilon)^c (t | f_(k-1)))product_(u in (s, t]) (1- tilde(Lambda)_(k,epsilon)^c (dif t | f_(k-1))) \
        &=^((*))-1/(1-Delta tilde(Lambda)^c_(k) (t | f_(k-1))) product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) integral_((s,t]) 1/(1 - Delta tilde(Lambda)_k^c (u |  f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_(k,epsilon) (dif u | f_(k-1)) \
        &quad +product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) 1/(1- Delta tilde(Lambda)_k^c (t |f_(k-1)))^2 evaluated(partial / (partial epsilon))_(epsilon=0) Delta tilde(Lambda)_(k,epsilon)^c (t | f_(k-1)) \
        &=-1/(1-Delta tilde(Lambda)^c_(k) (t |f_(k-1))) product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) integral_((s,t)) 1/(1 - Delta tilde(Lambda)_k^c (u | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_(k,epsilon) (dif u | f_(k-1)) \
        &quad -1/(1-Delta tilde(Lambda)^c_(k) (t | f_(k-1))) product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) integral_({t}) 1/(1 - Delta tilde(Lambda)_k^c (u | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_(k,epsilon) (dif u | f_(k-1)) \
        &quad +product_(u in (s, t]) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) 1/(1- Delta tilde(Lambda)_k^c (t | f_(k-1)))^2 evaluated(partial / (partial epsilon))_(epsilon=0) Delta tilde(Lambda)_(k,epsilon)^c (t | f_(k-1)) \
        &=^((**)) -product_(u in (s, t)) (1- tilde(Lambda)_k^c (dif t | f_(k-1))) integral_((s,t)) 1/(1 - Delta tilde(Lambda)_k^c (u | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_(k,epsilon) (dif u |  f_(k-1)).
$ <eq:derivcumhazard>
In $(*)$, we use the product rule of differentiation and a result for product integration (Theorem 8 of @gill1990survey), which states that the (Hadamard) derivative of the product integral
$mu mapsto product_(u in (s, t]) (1 + mu(u))$ in the direction $h$ is given by (for $mu$ of uniformly bounded variation)// it's always finite because; but not necessarily uniformly bounded for all cumhazards; unless we assume that cumhazards themsleves are uniformly bounded.
$
    &integral_((s,t]) product_(v in (s, u)) (1 + mu(dif v)) product_(v in (u, t]) (1 + mu(dif v)) h(dif u)
        &=product_(v in (s, t]) (1 + mu(dif v)) integral_((s,t]) 1/(1+Delta mu (u)) h(dif u).
$

In $(**)$, we use that
$integral_({t}) 1/(1 - Delta tilde(Lambda)_k^c (u | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) tilde(Lambda)^c_k (dif u | f_(k-1)) = 1/(1 - Delta tilde(Lambda)_k^c (t | f_(k-1))) evaluated(partial / (partial epsilon))_(epsilon=0) Delta tilde(Lambda)^c_(k,epsilon) (t | f_(k-1))$.
Furthermore, for $P_epsilon = P + epsilon (delta_((X,Y)) - P)$, a simple calculation yields the well-known result
$
    evaluated(partial / (partial epsilon))_(epsilon=0) mean(P_epsilon) [Y | X = x] = (delta_(X) (x)) / P(X = x) (Y - mean(P) [Y | X = x]).
$ <eq:derivcondexp>
Using @eq:iceipcw with @eq:derivcondexp and @eq:derivcumhazard, we have
$
    evaluated(partial / (partial epsilon))_(epsilon=0) Qbar(k-1) (tau, f_(k-1); P_epsilon) = delta_(historycensored(k-1) (f_(k-1)))/P(historycensored(k-1) = f_(k-1))  (macron(Z)^a_(k,tau) (tau) - Qbar(k-1) (tau) + A + B),
$
for $k=1, dots, K$,
where in the notation with $macron(Z)^a_(k,tau)$, we have made the dependencies explicit,
where
$
    A &:= integral_(eventcensored(k-1))^(tau) macron(Z)^a_(k,tau) (t_k, d_k, l_k, a_k, f_(k-1)) integral_((eventcensored(k-1), t_k)) 1/(1- Delta tilde(Lambda)_k^c (s | f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1))) (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
        &quad P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | f_(k-1)) \
        B &:=integral_(eventcensored(k-1))^(tau) (bb(1) {t_k < tau, d_(k) in {a, ell}})/(tilde(S)^c (t_k - | f_(k-1)))  ((bb(1) {a_k = 1}) / (densitytrtcensored(t_(k), k)))^(bb(1) {d_(k) = a}) evaluated(partial / (partial epsilon))_(epsilon=0) lr(Qbar(k) (P_epsilon | a_(k), l_(k),t_(k), d_(k), f_(k-1))) \
        & P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | f_(k-1)),
$
To get B, we use a similar derivation to the one given in @eq:stepTheorem1.
Now note that for simplifying A, we can write
$
    &integral_(eventcensored(k-1))^(tau) macron(Z)^a_(k,tau) (t_k, d_k, l_k, a_k, f_(k-1)) integral_((eventcensored(k-1),t_k)) 1/(1- Delta tilde(Lambda)_k^c (s | f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
        &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | historycensored(k-1) = f_(k-1)) \
        &= integral_((eventcensored(k-1),tau)) integral_(s)^tau macron(Z)^a_(k,tau) (t_k, d_k, l_k, a_k, f_(k-1)) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | historycensored(k-1) = f_(k-1)) \
        &#h(1.5cm) 1/(1- Delta tilde(Lambda)_k^c (s | f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
        &= integral_((eventcensored(k-1),tau)) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
        &#h(1.5cm) 1/(1- Delta tilde(Lambda)_k^c (s | f_(k-1))) 1/(tilde(S) (s - | historycensored(k-1) = f_(k-1)))  (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)) \
        &= integral_((eventcensored(k-1),tau)) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
        &#h(1.5cm) 1/(tilde(S)^c (s | historycensored(k-1) = f_(k-1)) S (s - | historycensored(k-1) = f_(k-1))) (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s)),
$
by an exchange of integrals. Here, we apply the result of @thm:iceipcw to get the last equation.
Hence, we have
$
    & evaluated(partial / (partial epsilon))_(epsilon=0) Qbar(k-1) (tau, f_(k-1); P_epsilon) \
        &= delta_(historycensored(k-1) (f_(k-1)))/P(historycensored(k-1) = f_(k-1))  (macron(Z)^a_(k,tau) (tau) - Qbar(k-1) (tau) + \            
            &quad+ integral_((eventcensored(k-1),tau)) (Qbar(k-1)(tau) - Qbar(k-1)(s)) \
            &#h(1.5cm) 1/(tilde(S)^c (s | historycensored(k-1) = f_(k-1)) S (s - | historycensored(k-1) = f_(k-1))) (tilde(N)^c (dif s) - tilde(Lambda)^c (dif s))) \
        &quad+ integral_(eventcensored(k-1))^(tau) (bb(1) {t_k < tau, d_(k) in {a, ell}})/(tilde(S)^c (t_k - | f_(k-1)))  ((bb(1) {a_k = 1}) / (densitytrtcensored(t_(k), k)))^(bb(1) {d_(k) = a}) evaluated(partial / (partial epsilon))_(epsilon=0) lr(Qbar(k) (P_epsilon | a_(k), l_(k),t_(k), d_(k), f_(k-1))) \
        &#h(1.5cm) P_((eventcensored(k), statuscensored(k), covariatecensored(k), treatcensored(k))) (dif (t_k, d_k, l_k, a_k) | f_(k-1)).
$ <eq:stepTheorem3>
Note that for $k=K+1$, the last term vanishes.
Therefore, we can combine the results from @eq:stepTheorem3 and @eq:baselineeif iteratively
to obtain the result, i.e. @eq:eif.

=

== Proof of @thm:adaptive <section:proofadaptive>
We find the following decomposition,
$
    hat(Psi)_n - Psi_tau^(g, K_"lim") (P) &= hat(Psi)_n - Psi_tau^(g, K_(n c)) (P) + Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P) \
        &= (bb(P)_n - P) phi_tau^(*, K_(n c)) (dot; P)  + Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P) + o_P (n^(-1/2)) \
        &= (bb(P)_n - P) phi_tau^(*, K_"lim") (dot; P) + (bb(P)_n - P) (phi_tau^(*, K_(n c)) (dot; P)- phi_tau^(*, K_"lim") (dot; P)) + Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P) + o_P (n^(-1/2)).
$ <eq:proofAdaptive>

@eq:proofAdaptive shows that we will have shown the result if
1. $Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P) = o_P (n^(-1/2))$.
2. $(bb(P)_n - P) (phi_tau^(*, K_(n c)) (dot; P)- phi_tau^(*, K_"lim") (dot; P)) = o_P (n^(-1/2))$.

To do so, we now show that $P(K_(n c) != K_"lim") -> 0$.
First define
$K_n = max_i tilde(N)_(tau i)$.
Then, we can certainly write that
$
    K_(n c) -  K_"lim" = K_(n c) - K_n + K_n - K_"lim",
$ <eq:Knlim>
By independence and definition of $K_n$, we have
$
    P(K_n != K_"lim") =^((a)) P(K_n < K_"lim") = P(tilde(N)_tau < K_"lim")^n -> 0.
$ <eq:Kn>
In $(a)$, we use that $N_t >= tilde(N)_t$ and the fact that $P(N_tau > K_"lim")=0$.
We now show that $P(K_(n c) < K_n) -> 0$ as $n -> oo$,
which will show that $P(K_(n c) != K_"lim") -> 0$ as $n -> oo$ by @eq:Knlim
and @eq:Kn.
We have, 
$
    P( K_(n c) != K_n) = P( union_(v=1)^(K_"lim") (sum_(i=1)^n bb(1) {tilde(N)_(tau, i) >= v} <= c))
        &<= sum_(v=1)^(K_"lim") P( sum_(i=1)^n bb(1) {tilde(N)_(tau, i) >= v} <= c) -> 0
$
as $n -> oo$. Here, we use that $sum_(i=1)^n bb(1) {tilde(N)_(tau, i) >= v}$ diverges almost surely to $oo$. Too see this, note that $sum_(i=1)^n bb(1) {N_(tau i) >= v}$ is almost surely monotone
in $n$, and $sum_(i=1)^n P(tilde(N)_(tau, i) >= v) = n P(tilde(N)_tau >= v) -> oo$.
From this and Kolmogorov's three series theorem, we conclude that $sum_(i=1)^n bb(1) {tilde(N)_(tau i) >= v} -> oo$
almost surely as $n -> oo$ and that $sum_(i=1)^n bb(1) {tilde(N)_(tau i) >= v} <= c$ has probability tending to zero as $n -> oo$ as desired.

Returning to showing 1 and 2, we now have that
$
    sqrt(n) (Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P)) = sqrt(n) bb(1) {K_(n c) != K_"lim"} (Psi_tau^(g, K_(n c)) (P) - Psi_tau^(g, K_("lim")) (P)) := E_n
$
and
$
    P(|E_n| > epsilon) <= P(K_(n c) != K_"lim") -> 0,
$
as $n -> oo$, so that 1 holds. A similar conclusion holds for 2, so the proof is complete.

=

== One-step procedure (the general case) <section:algorithmgeneral>

#algorithm("Debiased ICE-IPCW estimator (general)")[
    Input: Observed data $tilde(O)_i$, $i = 1, dots, n$, time horizon $tau < tauend$,
    and $K-1$.  Estimators of the propensity score $hat(pi)_0$, $hat(pi)_k$ for $k = 1, dots, K-1$
    and the censoring compensator $hat(Lambda)^c$. Estimates of $hat(S) (dot | historycensored(k-1)) = product_(s in (eventcensored(k-1), eventcensored(k))) (1 - sum_(x=a,ell,d,y) cumhazard(k,x,dif s))$.
    
    Output: One-step estimator $hat(Psi)_n$ of $Psi_tau^g (P)$; estimate of influence function $phi_tau^* (tilde(O); hat(P))$.
    1. Compute the ICE-IPCW estimator $hat(Psi)^0_n$ and obtain estimators of $Qbar(k)$ for $k = 0, dots, K-1$.
    2. Obtain estimates of $phi_tau^(*,"discrete") (tilde(O)_i; hat(P))$ for $i = 1, dots, n$ via @alg:onestepsimple.
    3. For $k = K - 1, dots, 1$:

       a. Estimate $Qbar(k-1) (u)$ for $u = t_1, dots, t_(m-1)$ where $0 < t_1 < dots < t_m = tau$
          by applying the following procedure: 

          - For each observation with $eventcensored(k-1) < u$ and $statuscensored(k-1) in {a, ell}$ compute the pseudo-outcome $hat(Z)^a_(k,tau)$ as follows:
              - If $statuscensored(k) = y$, calculate $hat(Z)^a_(k,tau)(u) =1 /(hat(S)^c (eventcensored(k)- | treatcensored(k-1), H_(k-1))) bb(1) {eventcensored(k) <= u, eventcensored(k) < tau}$.
              - Else if $statuscensored(k) = a$, evaluate $hat(Q)_(k+1) (tau, 1, H_(k))$ and calculate
              $
                  hat(Z)^a_(k,tau)(u) = 1/ (hat(S)^c (eventcensored(k)- | treatcensored(k-1), H_(k-1))) bb(1) {eventcensored(k) <= u, eventcensored(k) < tau} hat(Q)_(k+1) (tau, 1, H_(k)).
              $
              - Else if $statuscensored(k) = ell$, evaluate $hat(Q)_(k+1) (tau, treatcensored(k-1), H_(k))$,
                and calculate
              $
                  hat(Z)^a_(k,tau)(u)= 1/(hat(S)^c (eventcensored(k)- | treatcensored(k-1), H_(k-1))) bb(1) {eventcensored(k) < tau} hat(Q)_(k+1) (tau, treatcensored(k-1), H_(k)).
              $
          
          - Regress $hat(Z)^a_(k,tau) (u)$ on $(treatcensored(k-1), macron(H)_(k-1))$
            for the observations with $eventcensored(k-1) < u$ and $statuscensored(k-1) in {a, ell}$
            to obtain a prediction function $hat(Q)_(k) (u)$.
      b. Approximate the integral in @eq:eifMG using an integral approximation along the grid $t_1, dots, t_m$,
         that is:

        - Obtain estimates for each observation $i = 1, dots, n$
          $
              bb(1) {eventcensored(k) <= tau, statuscensored(k) = c} (Qbar(k-1) (tau)-Qbar(k-1) (eventcensored(k))) 1/(hat(S)^c (eventcensored(k) | historycensored(k-1)) hat(S) (eventcensored(k)- | historycensored(k-1)))
          $
          where we find an estimate of $Qbar(k-1) (eventcensored(k))$ by using the $u in {t_1, dots, t_m}$ closest to it. 
          (Only need to compute this for the individuals with $eventcensored(k-1) < tau$ and $statuscensored(k-1) in {a, ell}$
          who have followed the treatment regime up to $k-1$ events, i.e., $treatcensored(j) = 1$ for $j < k$)
        - Obtain estimates of the compensator term for each observation $i = 1, dots, n$
          $
              &sum_(j=1)^m bb(1) {eventcensored(k - 1) < t_j <= eventcensored(k) and tau} (Qbar(k-1) (tau)-Qbar(k-1) (t_j)) 1/(tilde(S)^c (t_j | historycensored(k-1)) S (t_j- | historycensored(k-1))) \
                  &quad times (cumhazardcensored(k,c,t_j)-cumhazardcensored(k,c,t_(j-1)))
          $
          (Only need to compute this for the individuals with $eventcensored(k-1) < tau$ and $statuscensored(k-1) in {a, ell}$
          who have followed the treatment regime up to $k-1$ events, i.e., $treatcensored(j) = 1$ for $j < k$)
        - Plug in the estimates in @eq:eifMG of the martingale term, and the propensity scores $hat(pi)_k$ and censoring weights $hat(S)^c$
          to obtain estimates of $phi_tau^(*, "MGc") (tilde(O)_i; hat(P))$ for $i = 1, dots, n$.
 
    4. Compute an estimate $phi_tau^* (tilde(O)_i; hat(P)) = phi_tau^(*,"MGc") (tilde(O)_i; hat(P)) + phi_tau^(*,"discrete") (tilde(O)_i; hat(P))$ for $i = 1, dots, n$.
    5. Compute the one-step estimator
       $
           hat(Psi)_n = hat(Psi)^0_n + 1/n sum_(i=1)^n phi_tau^(*) (tilde(O)_i; hat(P)).
       $
    6. Return $hat(Psi)_n$ and $phi_tau^* (tilde(O_i); hat(P))$ for $i = 1, dots, n$.
    
] <alg:one-stepgeneral>

=

== Additional simulation results <section:additionalsimresults>

=== Tables

==== Varying effects (A on Y, L on Y, A on L, L on A) -- uncensored case
#let time-confounding-legend = "Results for the case with time confounding"
#let vary_effects = (
    (name_file: "table_A_on_Y.csv",
        name_parameter: [$beta^y_A$]),
    (name_file: "table_L_on_Y.csv",
        name_parameter: [$beta^y_L$]),
    (name_file: "table_A_on_L.csv",
        name_parameter: [$beta^L_A$]),
    (name_file: "table_L_on_A.csv",
        name_parameter: [$alpha_L$]),
)

#for (name_file, name_parameter) in vary_effects [
    #let table_vary = csv("simulation_study/tables/" + name_file)
    #let _ = table_vary.remove(0)
    #figure(
        table(
            columns: table_vary.at(0).len(),
            fill: (_, y) => if ((calc.rem(y, 4) == 0 and y > 0) or (calc.rem(y, 4) == 1)) { gray.lighten(90%) },
            table.vline(x: 1),
            [#name_parameter], [*Estimator*], [*Coverage*],
            [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
            ..table_vary.slice(0, 4).flatten(),
            table.hline(),
            ..table_vary.slice(4, 8).flatten(),
            table.hline(),
            ..table_vary.slice(8, 12).flatten(),
        ),
        caption: [Results for the case with varying time-varying confounding (vary #name_parameter).
        The coverage, the mean squared error (MSE), average bias,
        standard deviation of the estimates, mean of the estimated standard error
            and the estimator applied are provided. ]
    )
]

==== Sample size -- uncensored case

#let table_sample_size = csv("simulation_study/tables/table_sample_size.csv")
#let _ = table_sample_size.remove(0)

#figure(
table(
    columns: table_sample_size.at(0).len(),
    fill: (_, y) => if ( y > 0) { gray.lighten(90%) },
    table.vline(x: 1),
        [$n$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
    ..table_sample_size.slice(0, 2).flatten(),
    table.hline(),
    ..table_sample_size.slice(2, 4).flatten(),
    table.hline(),
    ..table_sample_size.slice(4, 6).flatten(),
    table.hline(),
    ..table_sample_size.slice(6, 8).flatten(),
    
),
    caption: [Results for varying sample size ($n in {100,200,500,1000}$).
        The coverage, the mean squared error (MSE), average bias,
        standard deviation of the estimates, mean of the estimated standard error
        and the estimator applied are provided.]
)

=== Censoring

#let table_censored = csv("simulation_study/tables/table_censored.csv")
#let _ = table_censored.remove(0)

#for row_counter in (0, 1, 2, 3, 4, 5) [
    #figure(
        table(
            columns: (24%, 21%,auto,auto,auto,auto,auto),
            [*ICE model*], [*Estimator*], [*Cov.*],
            [*MSE*], [*Bias*], [*sd($hat(Psi)_n$)*], [*Mean($hat("SE")$)*],
            ..table_censored.slice(6*row_counter, 6*(row_counter+1)).map(x => x.slice(4,11)).flatten(),
        ),
        caption: [The table shows the results for the censored case for
            $(beta^y_A,beta^y_L,alpha_L,lambda_c)=(#table_censored.at(6*row_counter).slice(0,4).intersperse(", ").map(x => [#x]).join())$.
            The coverage, the mean squared error (MSE), average bias,
            standard deviation of the estimates, mean of the estimated standard error, the estimator (debiased ICE-IPCW and ICE-IPCW),
            and the pseudo-outcome model are provided],
    )
]

=== Boxplots

==== Varying effects (A on Y, L on Y, A on L, L on A) -- uncensored case

#let vary_effects = (
    (x: "A", y: "Y"),
    (x: "L", y: "Y"),
    (x: "A", y: "L"),
    (x: "L", y: "A"),
)

#for (x, y) in vary_effects [
    #figure(
        image("simulation_study/plots/boxplot_" + x + "_on_" + y + ".svg"),
        caption: [
            Boxplots of the estimates 
            for each estimator in each parameter setting for
            the cases with varying effects of #eval(x, mode: "math") on #eval(y, mode: "math").
            The lines indicates the true value of the target parameter $Psi_tau^g (P)$.            
        ],
    )

    #figure(
        image("simulation_study/plots/se_boxplot_" + x + "_on_" + y + ".svg"),
        caption: [
            Boxplots of the standard errors 
            for each estimator (LTMLE and debiased ICE-IPCW) in each parameter setting
            for the cases with varying effects of #eval(x, mode: "math") on #eval(y, mode: "math").
            The lines indicates the empirical standard error of the estimates for each estimator.
        ],
    )
]

==== Sample size -- uncensored case

#figure(
    image("simulation_study/plots/boxplot_sample_size.svg"),
    caption: [
        Boxplots of the estimates 
        for each estimator with varying sample size ($n in {100,200,500,1000}$).
        The line indicates the true value of the target parameter $Psi_tau^g (P)$.            
    ],
)

#figure(
    image("simulation_study/plots/se_boxplot_sample_size.svg"),
    caption: [
        Boxplots of the standard errors with varying sample size ($n in {100,200,500,1000}$)
        for the debiased ICE-IPCW estimator
        The line indicates the empirical standard error of the estimates.
    ],
)

== Discretizing time <sec:discretizing-time>
We briefly illustrate how to discretize the data into discrete-time data
consisting of $K$ time points with a target parameter that is the interventional absolute risk of a specified event
within time horizon $tau$, representing the usual longitudinal setting.
To do so, suppose that we have observed the processes $(L(t))_(t>=0)$, $(A(t))_(t>=0)$, and $(N^y (t))_(t>=0)$
at the time points $t_k = k times tau / K$ for $k = 0, dots, K$. Then, we put
$
    Y_k &= N^y (t_k), \
    L_k &= L (t_k), \
    A_k &= A (t_k).
$
Our data set then consists of $(L_0, A_0, Y_1, L_1, A_1, dots, Y_(K-1), L_(K-1), A_(K-1), Y_K)$,
which may then be applied with a discrete-time longitudinal causal inference estimator such
as LTMLE (@ltmle).


