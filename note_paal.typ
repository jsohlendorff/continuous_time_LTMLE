#import "@preview/fletcher:0.5.1": node, edge, diagram
// #import "template.typ": conf
#import "template/definitions.typ": *
#import "@preview/arkheion:0.1.0": arkheion
#import "@preview/ctheorems:1.1.3": *
#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#import "@preview/numty:0.0.5" as nt
#set cite(form: "prose")
// Color references red
#show  ref: it => {text(fill: maroon)[#it]}

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let proof = thmproof("proof", "Proof")

#show: arkheion.with(
    title: "A note on the potential outcomes framework in continuous time",
    authors: (
        (name: "Johan Sebastian Ohlendorff", email: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen"),
    ),
    abstract: [In this brief note, we consider the identification formulas of @ryalenPotentialOutcomes and compare it with the
        identification formula given in @rytgaardContinuoustimeTargetedMinimum2022, corresponding to their
        marked point process settings. It is shown that the resulting identification formulas
        are the same if and only if the probability of being treated given that you go to the doctor at time $t$ is equal to 1
        for Lebesgue-almost all $t$, provided that the transition hazards for dying are strictly positive for almost all $t$.
        //From this, we conclude that the identification formulas are quite different. 
    ]
    // Insert your abstract after the colon, wrapped in brackets.
    // Example: `abstract: [This is my abstract...]`
)
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

= Introduction

The aim of this note is to clarify potential differences between the
identification formulas of Helene and Pål. The target parameters are the same
in both setups. The target parameters are thus the risk of death at time $t$,
under the treatment regime which states that if you go to the doctor, you will be treated.
Throughout we consider a simple setting without censoring, without
time-varying covariates and without baseline covariates.

//We establish identification criteria for the causal effect of treatment on an outcome within this setting.

= Causal framework

Let us say that we are interested in
the effect of staying treated on being survival or death at time $t$.
We suppose that the event time $T$ is a positive continuous random variable $T tilde Q$ with say distribution function $F$.
The event time $T$ represents a counterfactual world in which
a patient may go to the doctor, but the doctor cannot make the decision not to treat the patient.

However, in the real world, doctors can make the decision to not treat the patient.
In the observed data $O = (T_((2)), T_((1)), D_((1)), A(T_((1)))) tilde P_(Q, G^*)$
and, as a shorthand, we let $P = P_(Q, G^*)$ be the probability law for both the observed data and the counterfactual world.
Here $T_((1))$ is the first event time in the sample, $D_((1))$ is the event status
(outcome $y$ or gone to the doctor $a$) at time $T_((1))$ and $A(T_((1)))$ is the treatment assignment at time $T_((1))$ ($A(T_((1))) in {0, 1}$).
$T_((2))$ is the terminal event time if the first event is not the terminal event.
We take $T_((2)) = oo$ otherwise. We suppose that $T_((1))$ is also a continuous random variable
and that $T_((2))$ is continuous if $D_((1)) != y$.

We can then formulate consistency as follows:
$
    T_((1)) = T " if " D_((1)) = y "or" T_((2)) = T " if " D_((1)) = a " and " A(T_((1))) = 1
$

Following @gill1997coarsening, we may then formulate Coarsening at Random as
$
    P(T_((1)) in dif tilde(t), D_((1)) = a, A(T_((1))) = 0 | T = t)
$
does not depend on $t$ for $tilde(t) < t$ (if either $D_((1)) = y$ or $D_((1)) = a$ and $A(T_((1))) = 1$, the variable is fully observed).

We can then let 
$
    G(tilde(t)) = P(T_((1)) <= tilde(t), D_((1)) = a, A(T_((1))) = 0 | T = t),
$
for $t > tilde(t)$.
Thus,
$
    G(t-) = lim_(tilde(t) -> t-) G(tilde(t)) = P(D_((1)) = a, A(T_((1))) = 0 | T = t)
$
which means that
$
    1- G(t-) = P(D_((1)) = y or (D_((1)) = a and A(T_((1))) = 1) | T = t)
$



Hence, we have that
$
    &P (T_((1)) <= t, D_((1)) = y or (T_((2)) <= t and D_((1)) = a and A(T_((1))) = 1))
        &=integral_0^t (1 - G(s-)) F(dif s) \
$
On the other hand,
$
    &P(T_((1)) <= t, D_((1)) = y) = integral_0^t exp(- integral_0^s Lambda^y (u) + Lambda^a (u) d u) Lambda^y (dif s) \
        &P(T_((1)) <= 2, D_((1)) =a, A_1 = 1)= integral_0^t exp(- integral_0^s Lambda^y (u) + Lambda^a (u) d u) integral_(s)^t exp(-Lambda^y (s,u)) Lambda^y (s,u) pi (s) Lambda^a (dif s) \ 
$
What this suggests is that we may use Inverse Probability Weighting to obtain
$
    Q(T <= t) &= mean(P) [1/(1-G(T_((1))-)) bb(1) {T_((1)) <= t, D_((1)) = y or (T_((2)) <= t and D_((1)) = a and A(T_((1))) = 1)}] \
        &=mean(P) [(1-bb(1) {T_((1)) <= t, D_((1)) = a, A(T_((1))) = 0}) /(1-G(T_((1))-)) bb(1) {T_((1)) <= t, D_((1)) = y or T_((2)) <= t}].
$ <eq:ipwpaalcar>
Letting $tau^A = T_((1)) "if " D_((1)) = a, A(T_((1))) = 0$ and $tau^A = oo$ otherwise
and $N_t (y) = bb(1) {T_((1)) <= t, D_((1)) = y or T_((2)) <= t}$ (observed outcome), we see that
$
    Q(T <= t) &= mean(P) [(bb(1) {tau^A > t}) / (1-G(T_((1))-)) N^y (t)],
$
which coincides Equation (29) of @ryalenPotentialOutcomes
if we can show that
$
    1-G(t-) = product_(s in (0,t)) (1-Lambda^a (t))
$
where $Lambda^a$ denotes the compensator of
$bb(1) {tau^A <= t}$. We can choose $Lambda^a$ on
the form,
$
    Lambda^a (t) = integral_0^t bb(1) { t<= T_((1))} Lambda
$
according to @last1995marked, which shows that they are the same. 

Note that if we assunme additionally that the $Lambda_t (dot)$ is locally independent of $T$,
we are in trouble. The observed data requires that the treatment is always administred in the observed data.

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
In light of the canonical compensator, we see immediately that the exchangeability condition is fulfilled if
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

    By our assumptions, $T_oo = oo quad P $-a.s. and 
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


= The intervened world

In a hypothetical world where the intervention is implemented all
persons are treated until death or $t$ years after the start of
treatment, whatever comes first. We could imagine that a pump is
inserted under the persons skin which injects the treatment and that
this pump cannot be removed or stopped by a general practitioner.

We further assume that there is absolutely no effect on death of
visiting the general practitioner in this hypothetical world. Hence,
the hypothetical world can be described with a simple two-stage model
and stochastic process $(X^*(s) in {0,1})_(s >= 0) (0 ="treated", 1="death")$. The target
parameter can be expressed as:

$
    P(X^*(t)=1) =integral_0^t exp(-integral_0^s h^*(u) d u) h^* (s) d s,
$

where $h^*$ is the hazard rate of transitions from state 0 to state 1.

We can as well use an irreversible three state model where death is
the only absorbing state and stochastic process $(X^(**)(s) in {0,1,2})_(s >= 0) (0="treated",
1="has visited Tivoli", 2="death")$. Here the irreversible intermediate
state is 'has visited Tivoli' which should not change the likelihood
of death. Note that since we assume absolutely no effect by visiting a
general practitioner we could simply exchange 'Tivoli' with 'visit to
a general practitioner' and the mathematical formula are not altered.
Let $P^(**)_(12) (s, t) = P(X^(**)(t)=2|X^(**)(s)=1)$
and $P^(**)_(02) (s, t) = P(X^(**)(t)=2|X^(**)(s)=0)$
In this model the basic assumption is
$
        P^(**)_(12) (s, t) = P^(**)_(02) (s, t)
$
for all $s<t$. Hence
bunting processes of the transitions
$
    N^(01,*)_t = N^(01,**)_t + N^(02,**)_t
$
Hence,
we can always find the intensity for $N^(01,**)_t$ and $N^(02,**)_t$ from the transition intensities for the "Tivoli" model, i.e.,
$
    h^(*) (t) bb(1) {t <= T^*} = h^(01,**)(t) bb(1) {t <= T^(*), Delta= 2}  + h^(02,**)(t) bb(1) {Delta = 1, macron(T) < t <= T^(*))} \
$
where $T^*$ denotes the terminal event time in the hypothetical world and $Delta$ denotes initial transition from state 0 to state 1 or 2,
$macron(T) = inf {t > 0 | N^(01,**)_t + N^(02,**)_t = 0}$. 
By writing up the target parameters in both settings, $h^(01,*)$ can easily be found
in terms of $h^(01,**), h^(02,**)$ and $h^(03,**)$. First note that
$
            P^(**)_(12) (s, t) &= integral_s^t exp(-integral_s^w (h^(12,**)(u)) d u) h^(12,**)(w) d w \
            P^(**)_(02) (s, t) &= integral_s^t exp(-integral_s^w (h^(01,**)(u) + h^(02,**)(u)) d u) h^(02,**)(w) d w 
$
so that
$
   integral_s^t exp(-integral_s^w (h^(12,**)(u)) d u) h^(12,**)(w) d w  = integral_s^t exp(-integral_s^w (h^(01,**)(u) + h^(02,**)(u)) d u) h^(02,**)(w) d w \
$
by the basic assumption.
$
    P(X^(**) (t) = 2) &= integral_0^t S^(**)_0( s-) (h^(02,**)(s) + integral_s^t exp(-integral_s^w h^(12,**)(u) d u) h^(12,**)(w) d w h^01 (s)) dif s \
        &=integral_0^t S^(**)_0( w-) h^(02,**)(w) d w+ integral_0^t integral_s^t exp(-integral_s^w h^(12,**)(u) d u) h^(12,**)(w) d w S^(**)_0( s-) h^01 (s) d s \
        &=integral_0^t S^(**)_0( w-) h^(02,**)(w) d w+ integral_0^t integral_0^s exp(-integral_s^w h^(12,**)(u) d u)(S^(**)_0( s-)) / (S^(**)_0( w-))  h^01 (s) d s S^(**)_0( w-) h^(12,**)(w) d w \
        &=integral_0^t S^(**)_0( w-) h^(02,**)(w) d w+ integral_0^t integral_0^s exp(-integral_s^w h^(12,**)(u) d u)S^(**)_0( s-) h^01 (s) d s h^(12,**)(w) d w \
        &=integral_0^t S^(**)_0( s-) h^(02,**)(s) d s \
        &+ integral_0^t exp(-integral_0^w h^(02,**)(u) d u) integral_0^s  exp(-integral_0^s h^(12,**)(u) d u)h^01 (s) d s h^(02,**)(w) d w  \
    P^(**)_(12)(s, t) h^(01,**)(s)) d s &= integral_0^t S^(**)_0( w-) (integral_0^t h^(12,**)(s) +1) h^(02,**)(s)d s \
    integral_0^t exp(-integral_0^s h^(*)(u) d u) h^(*)(s) d s \
        &= 1 - exp(-integral_0^t h^*(u) d u), \
$
What choice?
$
    &integral_0^t integral_0^s exp(-integral_s^w h^(12,**)(u) d u)(S^(**)_0( s-)) / (S^(**)_0( w-))  h^01 (s) d s S^(**)_0( w-) h^(12,**)(w) d w \
        &integral_0^t integral_0^s exp(-integral_s^w h^(12,**)(u) d u) exp(integral_s^w h^01(u)+h^02(u))  h^01 (s) d s S^(**)_0( w-) h^(12,**)(w) d w \
        &= integral_0^t integral_0^s exp(integral_0^w h^(01,**)(u) d u)  h^01 (s) d s S^(**)_0( w-) h^(02,**)(w) d w
$
Now note that 
$
    P(X^(**) (t) = 2) &= integral_0^t S^(**)_0( s-) (h^(02,**)(s) + integral_s^t S(w-) / (S(s)) h^(02,**)(w) d w h^01 (s)) dif s \
        &= integral_0^t S^(**)_0( s-) h^(02,**)(s) dif s + integral_0^t integral_s^t S(w-) h^(02,**)(w) d w h^01 (s) dif s \
        &= integral_0^t S^(**)_0( s-) h^(02,**)(s) dif s + integral_0^t integral_0^w h^01 (s) dif s S(w-) h^(02,**)(w) dif w \
        &= integral_0^t S^(**)_0( s-) (1 + H^01 (s))  h^(02,**)(s) dif s \
    P^(**)_(12)(s, t) h^(01,**)(s)) d s &= integral_0^t S^(**)_0( w-) (integral_0^t h^(12,**)(s) +1) h^(02,**)(s)d s \
    integral_0^t exp(-integral_0^s h^(*)(u) d u) h^(*)(s) d s \
        &= 1 - exp(-integral_0^t h^*(u) d u), \
$
where
$
    S^(**)_0 (s) &=exp(-integral_0^s (h^(01,**)(u) + h^(02,**)(u)) d u) \
$
Conversely, even under the basic assumption, there exist many choices of $h^(01,**)$
that will lead to the same $h^*(t)$, i.e., the basic assumption does not uniquely determine the transition intensities
in the "Tivoli" model. For example, $h^(01,**) (t) = 0$ can always be a choice. 

// If $h^(01,*)$, $h^(02,*)$ and $h^(12,*)$ are the transition intensities representing
// for the corresponding counterfactual world. Then, the basic assumption entails that
// $
//     h^(12,*) (t) = 1/(1 - integral_0^t exp(-integral_0^s (h^(01,*) (u) + h^(02,*) (u)) d u) h^(02,*) (s) d s) exp(-integral_0^s (h^(01,*) (u) + h^(02,*) (u)) d u) h^(02,*) (t)
// $
// To see this note,
// $
//     integral_0^t exp(-integral_0^s (h^(01,*) (u) + h^(02,*) (u)) d u) h^(02,*) (s) d s &= integral_0^t exp(-integral_0^s (h^(12,*) (u)) d u) h^(12,*) (s) d s \
//         &= 1 - exp(-integral_0^t h^(12,*) (u) d u)
// $
// from which the cumulative transition hazard of the transition from 1 to 2 is simply derived to be
// $
//     integral_0^t h^(12,*) (s) d s = - log (1 - integral_0^t exp(-integral_0^s (h^(01,*) (u) + h^(02,*) (u)) d u) h^(02,*) (s) d s)
// $
// and the result follows by differentiation.
// So, we can express the probability of dying in this multi-state model as:
// $
//     integral_0^t exp(-integral_0^s (h^(01,*) (u) + h^(02,*) (u)) d u) h^(02,*) (s) + h^(01,*) (s) integral_s^t exp(-integral_s^w (h^(01,*) (u) + h^(02,*) (u)) d u) h^(02,*) (w) d w d s
// $
// Similarly, $h^*$ can be expressed as
// $
//     1/(1 - integral_0^t exp(-integral_0^s (h^(01,*) (u) + h^(02,*) (u)) d u) h^(02,*) (s) + h^(01,*) (s) exp(-integral_s^t (h^(01,*) (u) + h^(02,*) (u)) d u) h^(02,*) (s)) exp(-integral_0^s (h^(01,*) (u) + h^(02,*) (u)) d u) h^(02,*) (t)
// $

= The observed world

The observed world is described by the four state multi-state model
depicted in @fig:multi-state. The model assumes that all persons are
treated at time 0 and then allows that some persons visit a general
practitioner without changing their treatment and others visit a
general practitioner which leads to stopping the treatment. We allow
for at most one visitation time per person that is the treatment can
only be stopped at a single date in time. We observe the counting
processes $N_t = (N^(01)_t, N^(02)_t, N^(03)_t, N^(13)_t, N^(23)_t)$
on the canonical filtered probability space $(Omega, cal(F),
(cal(F)_t)_(t >= 0), P)$, where $cal(F)_t = sigma(N_s | s <= t)$.
This means that we can represent the observed data as $O = (T_((1)),
D_((1)), T_((2)))$, where $T_((1))$ is the first event time, $D_((1))
in {01, 02, 03}$ is the first event type, $A(T_(1)) = bb(1) {D_1 !=
02}$ is the treatment at the first event time, and $T_((2))$ is the
second event time, possibly $oo$.  We will assume that the
distributions of the jump times are continuous and that there are no
jumps in common between the counting processes.  By a well-known
result for marked point processes (Proposition 3.1 of
@jacod1975multivariate), we know there exists functions $h^(i j)$,
such that the compensators $Lambda^(i j)$ of the counting processes
$N^(i j)$ with respect to $P-cal(F)_t$ are given by $ Lambda^(0 j) (d
t) &= bb(1) {t <= T_((1))} h^(0 j) (t) d t, quad j = 1, 2, 3 \
Lambda^(i 3) (d t) &= bb(1) {T_((1)) < t <= T_((2))} h^(i 3) (T_((1)),
t) d t, quad i = 2, 3 $

We let $S_0 (t) = prodint(s, 0, t) (1 - sum_j h^(0 j) (s) d s)$
and $S_1 (t | d, s) = prodint(u, s, t) (1 - sum_i h^(i 3) (s, u) bb(1) {d = i} d u)$ be the survival functions for the first and second event times, respectively.
Furthermore, denote by $P_(0 j) (t) = integral_0^t S_(s -) h^(0 j) (s) d s$ the probability of having an of type $j$ at time by time $t$
and $P_(i 3) (s, t) = integral_s^t S_1 (w- | d, s) h^(i 3) (s, w) d w$ be the probability of having a terminal at time $t$ given that the first event was of type $d$ at time $s$.
//As always, we will assume finite-variation martingales in the below, so that our underlying assumption that the counting proceses have no jumps in common implies that the martingales are orthogonal).

#figure(diagram(spacing: (5mm, 4.5mm), debug: false, node-stroke: 0.5pt, node-inset: 10pt, label-size: 7pt, {
    

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
    edgemsm(novisit, treat_visit, [$h^(01) (t)$])
    edgemsm(novisit, treat_visit_2, [$h^(02) (t)$])
    
    edgemsm(novisit, death, [$h^(03) (t)$])
    edgemsm(treat_visit, death, [$h^(13) (s, t)$])
    edgemsm(treat_visit_2, death, [$h^(23) (s, t)$])
    }

    msm_function(offset: (0,0), scale_text: 70%)
    let tint(c) = (stroke: c, fill: rgb(..c.components().slice(0,3), 5%))
    //node(label: [#align(top + right)[$P$]], enclose: ((-2.7, -0.3), (2.5, 3.3)),..tint(green))
    //msm_function(offset: (-1.5, 5), scale_text: 70%)
    //msm_function(offset: (2, 5), scale_text: 70%)
}), caption: [A multi-state model allowing one visitation time for the treatment with the possible treatment values 0/1. ])
<fig:multi-state>

= The potential outcomes framework
To follow along @ryalenPotentialOutcomes, we restrict the observations to the interval $[0, tau]$ for $tau > 0$.
We first need to define the intervention of interest,
defining the counting processes that we would have like to have observed under the intervention.
We can intervene on two components of $N$ $(N^02, N^01)$, defining the "interventional" processes as
$
    N^(g,0)_t &= 0 \
    N^(g,1)_t &= N^(01)_t + N^(02)_t \
$
This treatment regime defines that the doctor always treats the patient at the visitation time
and does not prevent the patient from visiting the doctor if they drop out of the treatment.
This thus dictates that an individual that transitioned from $0$ to $2$ should instead transition to $1$.
We define $T^(a, g)$ as the first time where the observed and the interventional process deviate.

Define also the single "intervention" process
$
    N^(g^*,0)_t = N^(g,0)_t = 0 \
$
where the interventional component is $N^02$. 
This dictates that an individual that transitioned from $0$ to $2$ should not transition to anything at that point. 
This intuitively thus means that a patient is prevented from visiting the doctor if they drop out of the treatment.
The key issue in @ryalenPotentialOutcomes is that we will not be able to differentiate between identification formulas for $g$ and $g^*$.
The reason is that the likelihood under the intervention only depends on the stopping time $T^a$ and the problem that the stopping time
$T^a$ is the same under $g$ and $g^*$.

To see this, let $T^(a, g^*)$ be the first time where the observed and the interventional process (according to $g^*$) deviate.
We have
$
    T^(a, g) &= inf_(t>0) {N^(g,0)_t != N^(01)_t} and inf_(t>0) {N^(g,1)_t != N^(02)_t} \
        &= inf_(t>0) {N^(02)_t != 0} and inf_(t>0) {N^(02)_t != 0} \
        &= inf_(t>0) {N^(02)_t != 0} \
$
Note that
$
    T^(a, g^*) = inf_(t>0) {N^(g^*,0)_t != 0} = inf_(t>0) {N^(g,0)_t != 0}
$
so that $T^(a, g^*) = T^(a, g)$.
Applying @thm:ryalen, we find that the identification formulas are the same because the weights $W_t$ are the same under $g$ and $g^*$.
Also note that $bb(1) {T^a <= t} = N^02 (t)$.
//prevents the patient from visiting the doctor if they drop out of the treatment.

//The issue in @ryalenPotentialOutcomes is that we will not be able to differentiate between $g$ and $g^*$ in the likelihood.
//The reason is that the likelihood under the intervention only depends on the stopping time $T^a$ and the problem that the stopping time
//$T^a$ is the same under $g$ and $g^*$.
//The compensator of the two counting processes are
//$
//    Lambda^(g,0) (d t) &= 0 \
//    Lambda^(g,1) (d t) &= h^(a) (t) pi_t (1) d t + h^(a) (t) (1 - pi_t (1)) d t = h^(a) (t) d t
//$

We now define the identification formula of interest in @ryalenPotentialOutcomes.
The outcome of interest is death at time $t$, i.e., 
$
    Y_t = N^(13)_t + N^(03)_t + N^(23)_t = bb(1) {T_1 <= t, D_1 = y} + bb(1) {T_2 <= t}
$
and we want to estimate $bb(E)_P [tilde(Y)_t]$ where $tilde(Y)_t$ denotes the outcome at time $t$, had the treatment regime (staying on treatment), possibly contrary to fact, been followed.

#theorem([Theorem 1 of @ryalenPotentialOutcomes])[
    We suppose that there exists a potential outcome process $(tilde(Y)_t)_(t in [0,tau])$ such that

1. Consistency: $tilde(Y)_t bb(1) {T^A > t} = Y_t bb(1) {T^A > t}$ for all $t > 0$ $P$-a.s.
2. Exchangeability: The $P-cal(F)_t$ compensators 
   $Lambda^(01)$, $Lambda^(02)$ are also compensators for $cal(G)_t=cal(F)_t or sigma(tilde(Y)_s, tau >= s >= 0)$.
   Here $tilde(Y)_s$ is added at baseline, so that $cal(G)_0 = sigma(tilde(Y)_s, tau >= s >= 0)$.
3. Positivity: $W_t = (bb(1) {T^A > t}) / (exp (-Lambda^02 (t))) = (1-bb(1){T_((1)) <= t, D_((1)) = a, A_((1)) = 0}) / exp(-integral_0^t bb(1) {s <= T_((1))} h^(a) (s) pi_s (0) d s)$#footnote[In the notation of @ryalenPotentialOutcomes, $tau^A = T^a$, $bb(N)_t = bb(1) {T^A <= t} = N_t^(02)$ and $ Lambda_t^(02)$ is the compensator of this process.]
   is a uniformly integrable martingale or equivalently that $R^"Pål"$ given by $d R^"Pål" = W_tau d P$ is a probability measure.
    
   Then the estimand of interest $Psi_t^"Ryalen": cal(M) -> RR_+$ is identifiable by
$
    Psi_t^"Ryalen" (P) := bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t] = bb(E)_(R^"Pål") [Y_t]
$
] <thm:ryalen>

From this, we can derive an alternate representation of the identification formula. We have that 
$
    Psi_t^"Ryalen" (P)  &= bb(E)_P [ bb(1) {T_((1)) <= t} Y_t W_t] + bb(E)_P [bb(1) {T_((2)) <= t} Y_t W_t] \
        &= bb(E)_P [ bb(1) {T_((1)) <= t} Y_t (1-bb(1) {T^a > t})/exp(-integral_0^(T_((1))) h^02 (s) d s)] \
        &qquad + bb(E)_P [bb(1) {T_((2)) <= t} Y_t (1-bb(1) {T^a > t})/exp(-integral_0^(T_((1))) h^02 (s) d s)] \
        &= bb(E)_P [ bb(1) {T_((1)) <= t, D_((1)) = 03} 1/exp(-integral_0^(T_((1))) h^02 (s) d s)] \
        &qquad+ bb(E)_P [bb(1) {T_((2)) <= t, D_((1)) = 01} 1/exp(-integral_0^(T_((1))) h^02 (s) d s)] \
        &= integral_0^t 1/exp(-integral_0^(t) h^02 (s) d s) P_03 (d t) \
        &qquad+ integral_0^t 1/exp(-integral_0^(t) h^02 (s) d s) P_13 (s, t) P_01 (d s) \
        &= integral_0^t exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u) h^03 (s) d s \
        &qquad + integral_0^t exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u)  P_13 (s, t) h^01 (s) d s \
$ <eq:ryalen>

== The identification formula in @rytgaardContinuoustimeTargetedMinimum2022

To discuss @rytgaardContinuoustimeTargetedMinimum2022, additionally define
$
    Lambda^(a) (t) &= (h^(01) (t) + h^(02) (t)) bb(1) {T_((1)) <= t} \
    pi_t (1) &= (h^(01) (t))/(h^(01) (t) + h^(02) (t)) 
$
Here, we can interpret $Lambda^(a) (t)$ as the cumulative intensity of the visitation times (i.e., $N_t^a = N^(01)_t + N^(02)_t$) and $pi_t (1)$ as the probability of being treated given that you go to the doctor at time $t$.
Furthermore, let $N_t^d = N^(03)_t + N^(13)_t + N^(23)_t$ be the counting process for the event of interest.
Then, its compensator is given by
$
    Lambda^d (d t) &= bb(1) {t <= T_((1))} h^(03) (t) d t \
        &+ bb(1) {T_((1)) < t <= T_((2))} (bb(1) {D_((1)) = 01}h^(13) (T_((1)), t) + bb(1) {D_((1)) = 02} h^(23) (T_((1)), t)) d t
$
Furthermore, let $A (t) = bb(1) {T_((1)) > t} + bb(1) {T_((1)) <= t, D_((1)) != 02}$ be the treatment process at time $t$.
Notationwise, we also define $Delta N (t) = N_t - N_(t-)$ for a cadlag process $N$.
@rytgaardContinuoustimeTargetedMinimum2022 give their likelihood as
$
    d P (O) &= prodint(t, 0, tau) (d Lambda^a (t) (pi_t (1))^(bb(1) {A(t)=1}) (1-pi_t (1))^(bb(1) {A(t)=0}) )^(Delta N^a (t)) (1 - d Lambda^a (t))^(1 - Delta N^a (t)) \
        &times prodint(t, 0, tau) (d Lambda^d (t)  )^(Delta N^d (t)) (1 - d Lambda^d (t))^(1 - Delta N^d (t)) \
        &= prodint(t, 0, tau) ((pi_t (1))^(bb(1) {A(t)=1}) (1-pi_t (1))^(bb(1) {A(t)=0}) )^(Delta N^a (t)) \
        &times prodint(t, 0, tau) (d Lambda^a (t))^(Delta N^a (t)) (1 - d Lambda^a (t))^(1 - Delta N^a (t)) (d Lambda^d (t)  )^(Delta N^d (t)) (1 - d Lambda^d (t))^(1 - Delta N^d (t)) \
        &= prodint(t, 0, tau) d G_t d Q_t 
$
where
$
    d G_t = ((pi_t (1))^(bb(1) {A(t)=1}) (1-pi_t (1))^(bb(1) {A(t)=0}) )^(Delta N^a (t)) \
    d Q_t = (d Lambda^a (t))^(Delta N^a (t)) (1 - d Lambda^a (t))^(1 - Delta N^a (t)) (d Lambda^d (t)  )^(Delta N^d (t)) (1 - d Lambda^d (t))^(1 - Delta N^d (d t)) \
$
Let $d G^*_t = ((1)^(bb(1) {A(t)=1}) (0)^(bb(1) {A(t)=0}) )^(Delta N^a (t)) = ((0)^(bb(1) {A(t)=0}))^(Delta N^a (t))$,
corresponding to staying on treatment.
Then define the interventional density as
$
    d P_(Q, G^*) (O) &= prodint(t, 0, tau) d G^*_t d Q_t 

$
and their target estimand $Psi_t^("Rytgaard") : cal(M) -> RR_+$ as
$
    Psi_tau^("Rytgaard") (P) = mean(P_(Q, G^*)) [N^d_tau] = integral_(cal(O)) y prodint(t, 0, tau) d G^*_t d Q_t 
    //integral_(cal(O)) y prodint(t, 0, tau) d G^*_t d Q_t 
$ <eq:rytgaardIntegral>
//where $cal(O)$ indicates that we integrate over the observed data and $y$ outcome at time $tau$.

We first need to define the integral in @eq:rytgaardIntegral.
To get a fully rigorous result, consider Proposition 1 in @ryalenPotentialOutcomes and Theorem 8.1.2 in @last1995marked.

//Calculate $mean(P) [d P_(Q, G^*) (O) bb(1) {T_1 < T_2 < oo} | history(2)]$.
First note that we have
$
    prodint(t, 0, tau) d G^*_t d Q_t = prodint(t, 0, t_((1))) d G^*_t d Q_t prodint(t, t_((1)), tau) d G^*_t d Q_t bb(1) {t_1 < t_2}
$
Let $Y_tau = bb(1) {T_((1)) <= tau, D_((1)) = 03} + bb(1) {T_((2)) <= tau} := Y^((1))_tau + Y^((2))_tau$ be death at time $tau$.
Then, note that
$
    y^((1))_tau (t_1, d_1) prodint(t, 0, t_((1))) d G^*_t d Q_t prodint(t, t_((1)), tau) d G^*_t d Q_t bb(1) {t_1 < t_2} =  y^((1))_tau prodint(t, 0, t_((1))) d G^*_t d Q_t
$
The second product integral evaluates to 1 because death at event 1 implies that all intensities are 0 after the first event.
//and because the counting processes cannot jump again after the first event ($0^0 = 1$).

We find
$
    prodint(t, 0, t_((1))) d G^*_t d Q_t &=  ((0)^(bb(1) {d_1 = 02}))^(bb(1) {d_1 in {01,02}})  (d Lambda^a (t_1))^(bb(1) {d_1 in {01, 02}}) (d Lambda^d (t_1)  )^(bb(1) {d_1 = 03}) \
        &qquad times prodint2(t, 0, t_((1))) (1 - d Lambda^d (t)) (1 - d Lambda^a (t))\
        &=  (d Lambda^a (t_1))^(bb(1) {d_1 in {01}}) (0 d t_1)^(bb(1) {d_1 in {02}})  (d Lambda^d (t_1)  )^(bb(1) {d_1 = 03}) S_0 (t_1-) \
        &=  ((h^01 (t_1)+h^02 (t_1)) d t_1)^(bb(1) {d_1 in {01}}) (0 d t_1)^(bb(1) {d_1 in {02}})  (h^03 (t_1) d t_1)^(bb(1) {d_1 = 03}) S_0 (t_1-) \
        &=  S_0 (t_1-) bb(1) {d_1 = 01} (h^01 (t_1) + h^02 (t_1)) d t_1 \
        &qquad +  S_0 (t_1-) bb(1) {d_1 = 03} h^03 (t_1) d t_1 
$
(compare with Equation (11) in @ryalenPotentialOutcomes). In the second equality, we used that the counting processes do not jump
at the same time with probability one to get $S(t_1) = prodint(t, 0, t_((1))) (1 - d Lambda^d (t)) (1 - d Lambda^a (t))$.
But multiplying with $y^((1))_tau$, we find
$
    y^((1))_tau prodint(t, 0, t_((1))) d G^*_t d Q_t = y^((1))_tau S(t_(1)-) bb(1) {d_1 = 03} h^03 (t_1) d t_1
$
Therefore, we have
$
    integral y^((1))_tau prodint(t, 0, t_((1))) d G^*_t d Q_t = integral_0^tau S(s-) h^03 (s) d s 
$
Similarly, we may find 
$
    & y^((2))_tau prodint(t, 0, t_((1))) d G^*_t d Q_t prodint(t, t_((1)), t_((2))) d G^*_t d Q_t bb(1) {t_1 < t_2 } \
        &=  y^((2))_tau bb(1) {t_1 < t_2}  S(t_1 -) bb(1) {d_1 = 01} (h^01 (t_1) + h^02 (t_1)) \
        &#h(1cm) times S(t_2 - | 01, t_1) h^(13) (t_1, t_2) d t_2 d t_1 \
$

// To that end, we have that 
// $
//     &P((T_((1)), D_((1)), T_((2))) in A times B times C, T_((2)) < oo) \
//         &= integral_A prodint2(u, 0, s) (1 - sum_(j) h^(0 j) (u) d u) \
//         &times (sum_(j in B) h^(0 j) (s) ((integral_C bb(1) {s < w} prodint2(u, s, w) (1 - h^(j 3) (s) d s) h^(j 3) (w) d w) bb(1) {j != 3})) d s \
//         &= integral_A prodint2(u, 0, s) (1 - (Lambda^a (s, 0) + Lambda^d (s, 0)) d u) \
//         &times (sum_(j in B) (bb(1) {j = 01} pi_s (1) Lambda^(a) (d s, 0) ((integral_C bb(1) {s < w} prodint2(u, s, w) (1 - h^(j 3) (s) d s) h^(j 3) (w) d w) bb(1) {j != 3} + bb(1) {oo in C, j = 3})) d s
// $
Thus the target estimand is
$
    Psi_tau^("Rytgaard") (P) &= integral_0^tau S_0 (s- ) h^03 (s) d s \
        &+ integral_0^tau S_0 (s- ) P_13 (s, tau) (h^01 (s) +h^02 (s)) d s 
$ <eq:rytgaard>

== Comparison of the approaches

We are now in a position, where we can readily compare the approaches in @rytgaardContinuoustimeTargetedMinimum2022 and
@ryalenPotentialOutcomes by considering the difference between @eq:rytgaard and @eq:ryalen. //The observational parameter of interest is identifiable by //Let $N_t = (N^(y)_t, N^(a)_t, N^(03)_t, N^(13)_t, N^(23)_t)$ be the multivariate counting process of the multi-state model.

//and let $N_t^(bullet) = N^(01)_t + N^(02)_t + N^(03)_t + N^(13)_t + N^(23)_t$ count the total number of events. 
//Given any measurable set $A$ we have there exists sets $B_0, B_1, B_2$ such that

Suppose that $h^02 (s) > 0$ and $h^13 (s, w) > 0$ for Lebesgue almost all $s, w$.
From this, we conclude that $Psi^("Rytgaard")_tau (P) = Psi_tau^"Ryalen" (P)$ if and only if $h^02 equiv 0$ a.e. if and only if $pi_t (1) equiv 1$ a.e.
(with respect to the Lebesgue measure restricted to $[0, tau]$).
To see this, note that
$
    Psi_tau^"Ryalen" (P)- Psi^("Rytgaard")_tau (P) &= integral_0^tau exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u)(1-exp( - integral_0^s h^02 (u) d u)) h^03 (s) d s \
        &+ integral_0^tau exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u) P_13 (s, tau) \
        &#h(3cm) times(1-exp( - integral_0^s h^02 (u) d u)) h^01 (s) d s \
        &+integral_0^tau S_0 (s-) P_13 (s, tau) h^02 (s) d s \
$ <eq:compare>
Since each term is non-negative, $Psi^("Rytgaard")_tau (P) = Psi_tau^"Ryalen" (P)$ implies that each term is equal to zero.
Since each of the integrands are non-negative, we must have that the integrands are equal to zero (almost surely). 
By letting $m_([0, tau])$ denote the Lebesgue measure on $[0, tau]$, we have for the first term in @eq:compare,
$
    exp( - sum_(j != 2) integral_0^s h^(0 j) (u) d u)(1-exp( - integral_0^s h^02 (u) d u)) h^03 (s) = 0 quad m_([0, tau])-"almost all" s &<=> \
    (1-exp( - integral_0^s h^02 (u) d u)) h^03 (s) = 0 quad m_([0, tau])-"almost all" s&<=> \
        (1-exp( - integral_0^s h^02 (u) d u)) = 0 quad m_([0, tau])-"almost all" s&<=> \
        h^02 (s) = 0 quad  m_([0, tau])-"almost all" s
$
with similar arguments for the second and third terms in @eq:compare.
// = Does the g-formula in @rytgaardContinuoustimeTargetedMinimum2022 have a causal interpretation? 

// We now consider the question concerning whether there is a causal interpretation of the g-formula in @rytgaardContinuoustimeTargetedMinimum2022.
// Given $W_t^*$ as in the next theorem, we can calculate that, $bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t^*] = Psi_t^("Rytgaard") (P)$.

// A simple result is given in the following theorem. Note that we can also formulated the exchangeability condition for each $t$ separately
// instead of formulating stochastic process conditions. 

// #theorem[
//     We suppose that there exists a potential outcome process $(tilde(Y)_t)_(t in [0,tau])$ such that

// 1. Consistency: $tilde(Y)_t bb(1) {T^A > t} = Y_t bb(1) {T^A > t}$ for all $t > 0$ $P$-a.s.
// 2. Exchangeability: We have
//    $
//        (tilde(Y)_t)_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)) 
//    $
// 3. Positivity: The measure given by $d R^"Helene" = W d P$ where $W^*_t = ((bb(1) {A(T_((1))) = 1}) / (pi_(T_(1)) (1)))^(N_t^01 +N^02_t)$ is a probability measure.

// Then the estimand of interest is identifiable by
// $
//     bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t] = bb(E)_(R^"Helene") [Y_t]
// $
// ]
// #proof[
//     Write $tilde(Y)_t = bb(1) {t < T_((1))} tilde(Y)_t + bb(1) {T_((1)) <= t} tilde(Y)_t$
//     Now, we see immediately that
//     $
//         bb(E)_P [ bb(1) {t < T_((1))} tilde(Y)_t] &= bb(E)_P [ bb(1) {t < T_((1))} tilde(Y)_t bb(1) {T^a > t}] \
//             &= bb(E)_P [ bb(1) {t < T_((1))} Y_t bb(1) {T^a > t}] \
//             &= bb(E)_P [ bb(1) {t < T_((1))} Y_t] \
//             &= bb(E)_P [ bb(1) {t < T_((1))} Y_t W_t] \
//     $
//     since $T^a$ must be $T_((1))$ if finite.  
//     On the other hand, we have that
//     $
//         bb(E)_P [ bb(1) {T_((1)) <= t} Y_t W_t] &= bb(E)_P [ bb(1) {T_((1)) <= t} bb(1) {T^a > t} Y_t W_t] \
//             &=bb(E)_P [ bb(1) {T_((1)) <= t} bb(1) {T^a > t} tilde(Y)_t W_t] \
//             &=bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t W_t] \
//             &=bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
//             &=bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t | A(T_((1))), D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
//             &=bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t | D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
//             &=bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t | D_1, T_1] bb(E)_P [((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a}) | T_1, D_1]] \
//             &= bb(E)_P [ bb(E)_P [ bb(1) {T_((1)) <= t} tilde(Y)_t | D_1, T_1] ] \
//             &= bb(E)_P [  bb(1) {T_((1)) <= t} tilde(Y)_t ]
//     $
//     which suffices to show the claim.
// ]

// With more than two events, though, the exchangeability condition becomes more difficult to interpret.
// In the case with at most three events, for the previous argument to go through, we would need the three exchangeability conditions
// $
//     (tilde(Y)_t bb(1) {T_((1)) <= t < T_((2))})_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)), \
//     (tilde(Y)_t bb(1) {T_((2)) <= t})_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)), \
//     (tilde(Y)_t)_(t in [0,tau]) perp A(T_((2))) | T_((2)), D_((2)), A(T_((1))), T_((1)), D_((1)), \
// $
// It would be interesting to see if there are some explicit conditions such that
// $
//     (tilde(Y)_t)_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)) 
// $
// implies the two first exchangeability conditions. An obvious one is if the event times are independent of the treatment given the history
// which is unlikely to hold.

// The next theorem gives a different causal interpretation of the g-formula in @rytgaardContinuoustimeTargetedMinimum2022.
// Unlike the previous theorem, the exchangeability wont have to be specified in terms of $tilde(Y)_t$ multiplied by a stochastic indicator function
// if there are more than two events. This issue is however that we are assuming the existence of multiple potential outcome processes and not just one.

// #theorem[
//     We suppose that there exists two potential outcome process $(tilde(Y)_(t,1))_(t in [0,tau])$ and $(tilde(Y)_(t,2))_(t in [0,tau])$ such that
//     these are potential outcomes of $Y_(t,1) = N^(03)_t$ and $Y_(t,2) = N^(13)_t+N^(23)_t$, respectively (the potential outcomes for each possible event where the outcome can occur).
//     Then we obviously define that
//     $tilde(Y)_t = tilde(Y)_(t,1) + tilde(Y)_(t,2)$ and $Y_t = Y_(t,1) + Y_(t,2)$.

//     1. Consistency: $tilde(Y)_(t,i) bb(1) {T^A > t} = Y_(t,i) bb(1) {T^A > t}$ for all $t > 0$ $P$-a.s for $i = 1, 2$.
// 2. Exchangeability: We have
//    $
//        (tilde(Y)_(t,i))_(t in [0,tau]) perp A(T_((1))) | T_((1)), D_((1)) 
//    $
//    for $i = 1, 2$.
// 3. Positivity: The measure given by $d R^"Helene" = W d P$ where $W_t = ((bb(1) {A(T_((1))) = 1}) / (pi_(T_(1)) (1)))^(N_t^01 +N^02_t)$ is a probability measure.

// Then the estimand of interest is identifiable by
// $
//     bb(E)_P [tilde(Y)_t] = bb(E)_P [Y_t W_t] = bb(E)_(R^"Helene") [Y_t]
// $
// ]
// #proof[
//     Now, we see immediately that
//     $
//         bb(E)_P [ Y_(t,1) W_t ] &= bb(E)_P [ tilde(Y)_(t,1) ]
//     $
//     because $tilde(Y)_(t,1)$ is always $Y_(t,1)$.
//     On the other hand, we have that
//     $
//         bb(E)_P [  Y_(t,2) W_t ] &=  bb(E)_P [  Y_(t,2) ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a}) ]\
//             &=bb(E)_P [  tilde(Y)_(t,2) ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
//             &=bb(E)_P [ bb(E)_P [ tilde(Y)_(t,2) | A(T_((1))), D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
//             &=bb(E)_P [ bb(E)_P [ tilde(Y)_(t,2) | D_1, T_1] ((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a})] \
//             &=bb(E)_P [ bb(E)_P [ tilde(Y)_(t,2) | D_1, T_1] bb(E)_P [((bb(1) {A(T_((1))) = 1}) / (pi_(T_((1))) (1)))^(bb(1) {D_((1)) = a}) | T_1, D_1]] \
//             &= bb(E)_P [ bb(E)_P [ tilde(Y)_(t,2) | D_1, T_1] ] \
//             &= bb(E)_P [  tilde(Y)_(t,2) ]
//     $
//     which suffices to show the claim.
// ]

#bibliography("references/ref.bib",style: "apa")
