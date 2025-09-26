#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
#import "@preview/colorful-boxes:1.4.3": *
#import "@preview/algo:0.3.6": *

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
    abstract: [?]
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
    W^g (t) &= product_(k=1)^(N_t) ((densitytrt(event(k), k)^(treat(k)) (1-densitytrt(event(k), k))^(1-treat(k))) / (densitytrt(event(k), k)^(treat(k)) (1-densitytrt(event(k), k))^(1-treat(k))))^(bb(1) {status(k) = a}) \
        &quad times (pi^*_0 (covariate(0))^(A(0)) (1-pi^*_0 (covariate(0)))^(1-A(0)))/ (pi_0 (covariate(0))^(A(0)) (1-pi_0 (covariate(0)))^(1-A(0))),
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

== One-step ICE-IPCW estimator <section:onestep>
We found that
$
        phi_tau^* (P) &= (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) sum_(k=1)^K product_(j = 1)^(k-1) ((bb(1) {treatcensored(j) = 1}) / (densitytrtcensored(eventcensored(j), j)))^(bb(1) {statuscensored(j) = a}) 1/( product_(j=1)^(k-1) tilde(S)^c (eventcensored(j)- | historycensored(j-1)))   \
            & times bb(1) {statuscensored(k-1) in {ell, a}, eventcensored(k-1) < tau} ((macron(Z)^a_(k,tau) (tau)- Qbar(k-1) (tau)) \
                &quad + integral_(eventcensored(k - 1))^(tau and eventcensored(k)) (Qbar(k-1) (tau)-Qbar(k-1) (u)) 1/(tilde(S)^c (u | historycensored(k-1)) S (u- | historycensored(k-1))) tilde(M)^c (dif u))\
            & +  Qbar(0) (tau) - Psi_tau^g (P),
$<eq:eif>
is the efficient influence function. 
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

//We have also elected not to estimate @eq:Qbaru using the procedure described in the algorithm in @alg:ipcwice (ICE-IPCW), as it
//may be prohibitively expensive to do so even along a sparse grid of time points,
//for flexible estimators.
Moreover, the resulting estimators are not guaranteed to be monotone in $u$
which $Qbar(k) (u | historycensored(k))$ is.
Applying flexible machine learning estimator may yet be possible if we apply a method that
can handle multivariate, potentially high-dimensional, outcomes,
such as neural networks. Note also
$
    (Qbar(k) (tau | historycensored(k-1)) - Qbar(k) (u | historycensored(k-1)))/(S (u | historycensored(k-1))) = S^c (u | historycensored(k-1)) mean(P) [Z^a_(k, tau) (tau | historycensored(k-1)) - Z^a_(k,tau) (u | historycensored(k-1)) | eventcensored(k) >= t, historycensored(k-1)],
$
which actually means that regression can be applied to estimate every term in the efficient influence function,
having estimated the cumulative cause-specific hazard functions for the censoring.

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

= Rates for the ICE-IPCW procedure
In this section, we discuss the rates of convergence for the ICE-IPCW estimator
and variations thereof.
Consider i.i.d. observations from $P_0 in cal(M)$
and a learner $cal(L)_o$ that maps
$cal(L)_o: (O_i)_(i=1)^n mapsto m_n$.
Let $cal(J)_(n k)$ be a collection of measurable functions
$f_k: [0, tauend] times cal(F)_k -> [0,1]$.
Furthermore, let
$
    cal(A)_(k u) := {h_u (O): h_u in L_2 (P), mean(P) [h_u | historycensored(k)] = Qbar(k+1) (u, historycensored(k)) }
$
for $u <= tau$. Consider the squared error loss
$L: cal(Z) times cal(F)_(k)$ where $L(m, f) := (m(f) - f)^2$.

We consider the least squares regression estimator given by
$
    m_(k,n) (u) := "argmin"_(f in cal(J)_(n k)) 1/n sum_(i=1)^n (macron(Z)^a_(k, tau) (u) (hat(S)^c, m_(k+1, n)) - f (historycensored(k)))^2
$

x


Recall the definitions $Qbar(K): (a_k, h_k) mapsto 0$ and define recursively, for $k = K, dots, 0$,
$
        macron(Z)^a_(k, tau) (u) =
        1/(tilde(S)^c (eventcensored(k) - | treatcensored(k-1), macron(H)_(k-1))) &(bb(1) {eventcensored(k) <= u,eventcensored(k) < tau, statuscensored(k) = a}
        Qbar(k) (1, macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, eventcensored(k) < tau, statuscensored(k) = ell} Qbar(k) (treatcensored(k), macron(H)_k) \
            &quad+ bb(1) {eventcensored(k) <= u, statuscensored(k) = y}),
$
and
$
   Qbar(k): (u, a_k, h_k) mapsto mean(P) [macron(Z)^a_(k+1, tau) (u) | treatcensored(k) = a_k, macron(H)_(k) = h_k], quad u <= tau
$
where $h_k = (a_k, l_k, t_k, d_k, dots, a_0, l_0)$.
However, in practice, we need to estimate $Qbar(k)$ and $tilde(S)^c$
since these are unknown quantities.
We may denote these by $m_(k+1,n)$ and $hat(S)^c$;
whence estimates of the pseudo-outcomes $macron(Z)^a_(k, tau) (hat(S)^c, m_(k+1, n))$ can be obtained.
After this we can apply our regression estimator of choice.
Let $m_(k,n)$ be an estimator of $Qbar(k)$ obtained
in this way and let $m^*_(k,n)$ denote the estimate
obtained by regressing $macron(Z)^a_(k, tau)$
directly on the history $historycensored(k)$.
This is the oracle estimator
in which we use the true values of $tilde(S)^c$ and
$Qbar(k+1)$.
An elementary bound gives,
$
    integral (Qbar(k) (u; f_k) - m_(k,n) (u, f_k)^2 P (dif f_k)
        &<= 2 integral (Qbar(k) (u; f_k) - m^*_(k,n) (u, f_k))^2 P (dif f_k) \
        &quad + 2 integral (m^*_(k,n) (u, f_k) - m_(k,n) (u, f_k))^2 P (dif f_k)
$
The first term on the right-hand side can be known if one knows
the convergence rate of the regression estimator used.
However, the second term is evidently more difficult.
To relax this problem, we consider specifically the case
when the regression estimator is a least squares regression
estimator, i.e., $m_(k,n)$ minimizes
$
    m_(k,n) := "argmin"_(f in cal(F)_n) 1/n sum_(i=1)^n (macron(Z)^a_(k, tau) (hat(S)^c, m_(k+1, n)) - f (historycensored(k)))^2
$
Similarly, $m^*_(k,n)$ minimizes
$
    m^*_(k,n) := "argmin"_(f in cal(F)_n) 1/n sum_(i=1)^n (macron(Z)^a_(k, tau) (tilde(S)^c, Qbar(k+1)) - f (historycensored(k)))^2 
$
The estimators are related in the following way.
$
    m_(k,n) <= 2/n sum_(i=1)^n (macron(Z)^a_(k, tau) (hat(S)^c, m_(k+1, n)) - macron(Z)^a _(k, tau) (tilde(S)^c, Qbar(k+1)))^2 +2 m^*_(k,n)
$
We can write
$
    &integral (m^*_(k,n) (u, f_k) - m_(k,n) (u, f_k))^2 P (dif f_k) \
        &= 
$
// Notes: van der laan bound in Lemma 5.3, bounds in terms of previous regression and pi (here can use lemma 19.24 of van der vaaart)
// and for the second term involving vc dimension, we should be able to use some other bracketing number. 


//         &<=//  integral (m^*_(k,n) (u, f_k) - m_(k,n) (u, f_k))^2 (P (dif f_k) - bb(P)_n (dif f_k)) \
//         &+ 2/n sum_(i=1)^n (macron(Z)^a_(k, tau) (hat(S)^c, m_(k+1, n)) - m_(k,n) (u, f_k))^2 \
//         &+ 2/n sum_(i=1)^n (macron(Z)^a_(k, tau) (tilde(S)^c, Qbar(k+1)) - m^*_(k,n) (u, f_k))^2 \
// $

// = Discussion

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

One other direction is to use Bayesian methods. Bayesian methods may be particular useful for this problem since they do not have issues with finite sample size.
They are also an excellent alternative to frequentist Monte Carlo methods for estimating the target parameter with @eq:cuminc
because they offer uncertainty quantification directly through simulating the posterior distribution
whereas frequentist simulation methods do not.

We also note that an iterative pseudo-value regression-based approach (@andersen2003pseudovalue) may also possible, but is
not further pursued in this article due to the computation time of the resulting procedure. Our ICE IPCW estimator
also allows us to handle the case where the censoring distribution depends on time-varying covariates.
//  However, nonparametric Bayesian methods are not (yet) able to deal with a large number of covariates.

There is also the possibility for functional efficient estimation using the entire interventional cumulative incidence curve
as our target parameter. There exist some methods for baseline interventions in survival analysis
(@onesteptmle @westling2024inference).

#bibliography("references/ref.bib",style: "apa")

= Appendix

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
