#import "definitions.typ": *
#import "@preview/tablem:0.2.0": tablem, three-line-table
#import "@preview/colorful-boxes:1.4.3": *
#set heading(numbering: "1.")
#let example = thmplain("example", "Example").with(numbering: "1.")
#set math.equation(numbering: "(1)")
#show table.cell.where(y: 0): strong
#set table(
  stroke: (x, y) => if y == 0 {
    (bottom: 0.7pt + black)
  },
  align: (x, y) => (
    if x > 0 { center }
    else { left }
  )
)
#show: thmrules.with(qed-symbol: $square$)
#show math.equation: it => {
  if it.block and not it.has("label") [
    #counter(math.equation).update(v => v - 1)
    #math.equation(it.body, block: true, numbering: none)#label("")
  ] else {
    it
  }  
}

#outline()

= Simulating longitudinal data for time-to-event analysis in continuous time

We simulate a cohort of patients who initiate treatment at time $t = 0$, denoted by $A(0) = 1$
and who are initially stroke-free, $L(0) = 0$.
All individuals are followed for up to $tauend = 900 "days"$ or until death.
Initially, we do not consider censoring or competing events. 
During follow-up, patients may experience (at most) one stroke, stop treatment (irreversibly), and die,
that is $N^x (t) <= 1$ for $x = a, ell, y$.
With these assumptions $K=2$ in the main note (at most two non-terminal events).
The primary outcome is the _risk of death within $tau = 720$ days_.

Our observations consist of
$
    O = (event(3), status(3), treat(2), covariate(2), event(2), status(2), treat(1), covariate(1), event(1), status(1), treat(0), covariate(0), "age"),
$
where $event(k)$ is the time of the $k$'th event, $status(k) in {ell, a, y}$ (stroke, visit, death),
$treat(k)$ is the treatment status at time $event(k)$, and $covariate(k)$ is the value of the covariate at time $event(k)$.
Note that we let $event(k) = oo$ if the $k$'th event cannot happen (because the previous event was a terminal event or the end of the study period was reached)
or if the $k$'th event occurs after the end of the study period.
Let Exp($lambda$) denote the exponential distribution with rate $lambda >= 0$.
We let $lambda = 0$ correspond to the case that the event cannot happen, i.e., $T_((1))^x = oo$.

Then, we generate the baseline variables as follows
$
    &"age" tilde "Unif"(40,90), \
        &L = 0, \
        & treat(0) = 1,
$

Now we describe the simulation mechanism corresponding to the first event that can happen.
We define $T_((1))^a$ such that the patient can be expected
to go to the doctor within the first year,
if the two other events have not occurred first.
As the first event, we draw
$
    &T_((1))^x  tilde "Exp"(lambda^x_1 exp(beta^x_(1,"age") "age"+ beta^x_(1,"A") treat(1) + beta^x_(1, "L") covariate(1))), x = ell, y \
        &T_((1))^a tilde 1 + cal(N)(0, delta) \
        &status(1) = "argmin"_(x = a, ell, y) T_((1))^x \
        &event(1) = T_((1))^status(1) \
        &treat(1) | event(1) = t, "age" = x cases(tilde "Bernoulli(expit"(alpha_(10) + alpha_(1, "age") x) "if" status(1) = a, 1 "otherwise") \
        &covariate(1) = 1, \
$
Note that we simulate from a "competing event setup" by defining latent variables $T_((1))^x$ for each possible event type $x$.

We now describe the second event that can happen.
If the first event was a terminal event -- either outcome or that the previous event happened after the end of the study period --
we stop and do not generate more data for this patient.
Now, we let $S_((2))$ denote the time between $event(1)$ and the second event $event(2)$,
i.e., $S_((2)) = event(2) - event(1)$.
As we required that $N^x (t) <= 1$,
if the first event was a stroke, we cannot have a second stroke,
and if the first event was a visit, we cannot have a second visit.
If the first event was a stroke, the doctor visit is likely to happen soon after,
so we simulate the corresponding latent time as an exponential random variable.
We will then generate the second event time $event(2)$ as follows:

$
    &S_((2))^ell tilde "Exp"(lambda^ell_2 exp(beta^ell_(2,"age") "age" + beta^ell_(2, A) treat(1)) bb(1) {status(1) = a}) \
        &S_((2))^y tilde "Exp"(lambda^y_2 exp(beta^y_(2,"age") "age" + beta^y_(2, A) treat(1) + beta^ell_(2, L) covariate(1))) \ 
        &S_((2))^a tilde "Exp"(gamma_0 exp(gamma_"age" "age") bb(1) {status(1) =ell}) \
            &status(2) = "argmin"_(x = a, ell, y,) S_((2))^x \
            &event(2) = event(1) + S_((2))^status(2) \
        &treat(2) | event(2) = t, "age" = x, treat(1) = a_1, covariate(1) = l_1 \
        &qquad =cases(tilde "Bernoulli(expit"(alpha_(20) + alpha_(2, "age") x + alpha_(2, "L") l_1)")" "if" status(2) = a, 1 "otherwise") \
        &covariate(2) = 1. \
$

Finally, we let $event(3) = S_((3)) + event(2)$ denote the time of the third event,
if it can happen.
We define the time $S_((3))$ as follows:
$
    S_((3))^y tilde "Exp"(lambda^y_3 exp(beta^y_(3,"age") "age" + beta^y_(3, A) treat(2) + beta^y_(3, L) covariate(2))) \
    status(3) = y \
    event(3) = event(2) + S_((3))^status(3).
$
Here, we furthermore make the assumption that
it does not matter whether the patient had a stroke first
and then visited the doctor, or visited the doctor first and then had a stroke.
Also, we assumed that the previous event times have no influence on anything,
only the "marks". However, this may be unrealistic, as the effect of a stroke on mortality may naturally decrease over time.

When the static intervention is applied, we put $treat(k) = 1$ for each $k = 1, dots, K$.
Some explanation for this is (probably) warranted (see @sec:intensities).

@sec:target-estimand details the target estimand and how to arrive at the iterative conditional expectation formula.
Also, we discuss how to use the algorithm in practice for the simple
data generating mechanism.
In @sec:simulation-study, we present a simulation study
to illustrate the algorithm and the target estimand
with time-varying confounding and censored data.
Finally, the mechanism detailed here may be too simplistic.
We discuss extensions in @sec:extensions.

//It is not too difficult to see that the likelihood factorizes as in #cite(<rytgaardContinuoustimeTargetedMinimum2022>, form: "prose")
//corresponding to the intervention that we are interested in (see e.g., Theorem II.7.1 of #cite(<andersenStatisticalModelsBased1993>, form: "prose")).

== Plain Language Summary (for Clinical Audience)

We simulate patients who all begin treatment and are initially healthy.
Over two years, they may have a stroke, stop treatment (only at doctor visits), or die.
A routine doctor visit is scheduled about a year after treatment begins,
unless a stroke happens first, in which case a visit is likely to occur soon after.
Doctors are less likely to stop treatment after a stroke.
The chance of dying depends on whether the patient has had a stroke and whether they are still on treatment.

= Target estimand and example usage of algorithm <sec:target-estimand>

We explain here what the target estimand is
and how to arrive at the iterative conditional expectation formula.
Recall that 
$
    history(0) &= (treat(0), covariate(0)),\
    history(1) &= (event(1), status(1), treat(1), covariate(1), treat(0), covariate(0), "age"), \
    history(2) &= (event(2), status(2), treat(2), covariate(2), event(1), status(1), treat(1), covariate(1), treat(0), covariate(0), "age"),
$
Let $cumhazard( k, x, t)$ denote the cumulative cause-specific hazard function
for $event(k)$ and $status(k) = x$ at time $t$ given the history $history(k-1)$.
For instance, if $k=2$ and $x=y$, then in the simulation mechanism, we have
$
    cumhazard(2, y, t) = lambda^y_2 exp(beta^y_(2, "age") "age" + beta^y_(2, A) treat(1) + beta^y_(2, L) covariate(1)) 
$
Furthermore, let $densitytrt(t,k)$ denote the probability of being treated as the $k$'th event
given that you go to the doctor at time $t$, i.e., $status(k)=a$,
and your history $history(k-1)$. We let, for convenience of notation, "age" be included in $L (0)$.

Using the notation $f_(t_k) = (t_k, d_k, a_k, l_k, dots, a_0, l_0)$
with $f_0 = (a_0, l_0)$, we, analogously to @rytgaardContinuoustimeTargetedMinimum2022, define our target parameter $Psi_tau : cal(P) -> RR$
for a non-parametric model $cal(P)$ as
$
    Psi_tau (P) &= integral (integral_((0, tau]) (integral_((t_1,tau]) (integral_((t_2,tau])  product_(w_3 in (t_3, tau)) (1 - Lambda^y_3 (dif w_3 | f_(t_2))) Lambda_3^y (dif t_3 | f_(t_2))) \
        &qquad times  product_(w_2 in (t_2, tau)) (1 - sum_(x=a,y) Lambda^x_2 (dif w_2 | f_(t_1))) bb(1) {a_2=1} times Lambda_2^a (dif t_2 | f_(t_1))) \
        &qquad times product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_0))
        Lambda_1^ell (dif t_1 | f_0) )P_(L(0)) (dif l_0) \
        &+integral (integral_((0, tau]) (integral_((t_1,tau]) (integral_((t_2,tau])  product_(w_3 in (t_3, tau)) (1 - Lambda^y_3 (dif w_3 | f_(t_2))) Lambda_3^y (dif t_3 | f_(t_2))) \
        &qquad times  product_(w_2 in (t_2, tau)) (1 - sum_(x=y,ell) Lambda^x_2 (dif w_2 | f_(t_1))) Lambda_2^ell (dif t_2 | f_(t_1))) \
        &qquad times product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_0))
        bb(1) {a_1 = 1} times Lambda_1^a (dif t_1 | f_0) )P_(L(0)) (dif l_0) \
        &+integral (integral_((0, tau]) (integral_((t_1,tau])  product_(w_2 in (t_2, tau)) (1 - sum_(x=a,y) Lambda^x_2 (dif w_2 | f_(t_1)))  Lambda_2^y (dif t_2 | f_(t_1))) \
        &qquad times product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_0))
        Lambda_1^ell (dif t_1 | f_0) )P_(L(0)) (dif l_0) \
        &+integral (integral_((0, tau]) (integral_((t_1,tau])  product_(w_2 in (t_2, tau)) (1 - sum_(x=a,y) Lambda^x_2 (dif w_2 | f_(t_1))) Lambda_2^y (dif t_2 | f_(t_1))) \
        &qquad times product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_0))
        bb(1) {a_1=1} times Lambda_1^a (dif t_1 | f_0) )P_(L(0)) (dif l_0) \
        &+integral (integral_((0, tau]) product_(w_1 in (t_1, tau)) (1 - sum_(x=a,y,ell) Lambda^x_1 (dif w_1 | f_(0))) Lambda_1^y (dif t_1 | f_(0))) P_(L(0)) (dif l_0), \
        &:= zeta_1 (P) + zeta_2 (P) + zeta_3 (P) + zeta_4 (P) + zeta_5 (P) 
    
$
corresponding to setting $densitytrt(t, k) = 1$.
This expression is fairly long and quite complicated.

We now explain how one goes from this apparently complicated expression
to the iterative conditional expectation formula,
which reduces the dimensionality of the problem significantly.

#example[
    Let,
    $
        &Z^a_3 = bb(1) {event(3) <= tau}, \ \
    &Qbar(2) (f_(t_2)) \
            &= mean(P) [Z^a_3 | history(2) = f_(t_2)], \ \
            &Z^a_2 = bb(1) {event(2) <= tau, status(2) = y} + bb(1) {event(2) < tau, status(2) = ell} Qbar(2) (history(2)) + 
        bb(1) {event(2) < tau, status(2) = a} Qbar(2) (cal(F)^bold(1)_(event(2))) \
        
        &Qbar(1) (f_(t_1)) \
        &= mean(P) [Z_2^a | history(1) = f_(t_1)], \ \

            &Z^a_1 = bb(1) {event(1) <= tau, status(1) = y} + bb(1) {event(1) < tau, status(1) = ell} Qbar(1) (history(1)) +
        bb(1) {event(1) < tau, status(1) = a} Qbar(1) (cal(F)^bold(1)_(event(1))) \
        &Qbar(0) (f_0) \
        &= mean(P) [Z_1^a | history(0)=f_0],
$
and 
$
    cal(F)^bold(1)_(event(2)) &= (event(2), status(2), 1, covariate(2), event(1), status(1), treat(1), covariate(1), treat(0), covariate(0), "age"),\
    cal(F)^bold(1)_(event(1)) &= (event(1), status(1), 1, covariate(1), treat(0), covariate(0), "age"),
$
    which is the history where we set the _current_ treatment to 1.
Then, $Psi_tau (P) = mean(P_(L(0))) [Qbar(0) (history(0))]$,
    where $P_(L(0))$ is the distribution of the baseline confounders.
] <example:ice>
#proof[

First note that,

$
    &P (event(k) <= t, status(k) = x | history(k-1) = f_(t_(k-1))) \
        &= integral_((t_(k-1), s]) product_(u in (t_(k-1), s)) (1 - sum_(x=a,ell,y) Lambda^x_k (dif u | f_(t_(k-1)))) Lambda^x_k (dif s | f_(t_(k-1))) , t < tauend
$
for $x = y, ell$ by definition
and
$
    &P (event(k) <= t, status(k) = a, treat(k) = 1 | history(k-1) = f_(t_(k-1))) \
        &qquad = integral_((t_(k-1), s]) product_(u in (t_(k-1), s)) (1 - sum_(x=a,ell,y) Lambda^x_k (dif u | f_(t_(k-1)))) pi_k (event(k), history(k-1)) Lambda^a_k (dif s | f_(t_(k-1))) 
$
Using this, we now see that
$
        zeta_1 (P) &= mean(P_(L(0))) [mean(P) [bb(1) {event(1) < tau, status(1) = ell}  mean(P) [ bb(1) {event(2) < tau, status(2) = a} (bb(1) {treat(2)=1})/(pi_2 (event(2), history(1)))  \
            &qquad qquad times mean(P) [bb(1) {event(3) <= tau} | history(2)] | history(1) ] | history(0)] ] \
    &= mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))) \
            &qquad times mean(P) [ bb(1) {event(2) < tau, status(2) = a} (bb(1) {treat(2)=1})/(pi_2 (event(2), history(1)))  \
                &qquad qquad times mean(P) [bb(1) {event(3) <= tau} | history(2)] | history(1) ] | history(0)] ] \
$ 
and
    $
        zeta_2 (P) &= mean(P_(L(0))) [mean(P) [bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))  mean(P) [ bb(1) {event(2) < tau, status(2) = ell}  \
            &qquad qquad times mean(P) [bb(1) {event(3) <= tau} | history(2)] | history(1) ] | history(0)] ] \
            &=mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))) \
                &qquad times mean(P) [ bb(1) {event(2) < tau, status(2) = ell} times mean(P) [bb(1) {event(3) <= tau} | history(2)] | history(1) ] | history(0)] ] \
    $ 
Here, we simply add terms which are zero corresponding to two treatments and two strokes.
Similarly, we find
$
    zeta_3 (P) &= mean(P_(L(0))) [mean(P) [bb(1) {event(1) < tau, status(1) = ell} mean(P) [bb(1) {event(2) <= tau, status(2) = y} | history(1)] | history(0)] ] \
    zeta_4 (P) &= mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = a}) /(pi_1 (event(1), history(0))) bb(1) {treat(1) = 1} mean(P) [bb(1) {event(2) <= tau, status(2) = y} | history(1)] | history(0)] ] \
    zeta_5 (P) &= mean(P_(L(0))) [mean(P) [bb(1) {event(1) <= tau, status(1) = y}  | history(0)] ] \
$
First, we need to note that,
$
    &mean(P) [ bb(1) {event(2) < tau, status(2) = a} (bb(1) {treat(2)=1})/(pi_2 (event(2), history(1))) Qbar(2) (history(2)) | history(1) ]\
        &=mean(P) [ bb(1) {event(2) < tau, status(2) = a} (bb(1) {treat(2)=1})/(pi_2 (event(2), history(1))) Qbar(2) (cal(F)^bold(1)_(event(2))) | history(1) ]\
        &=mean(P) [ bb(1) {event(2) < tau, status(2) = a} (mean(P) [bb(1) {treat(2)=1} | history(1), status(2), event(2) ])/(pi_2 (event(2), history(1))) Qbar(2) (cal(F)^bold(1)_(event(2))) | history(1) ]\
        &=mean(P) [ bb(1) {event(2) < tau, status(2) = a} Qbar(2) (cal(F)^bold(1)_(event(2))) | history(1) ],
$
Here, we use the iterated law of conditional expectations and that $pi_2 (event(2), history(1))$ is the probability of being treated at time $event(2)$ given the history $history(1)$
and that you visit the doctor as the second event. Using this, we can rewrite
$zeta_1 (P)$ as follows:
$
    zeta_1(P) &= mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))) \
        &qquad times mean(P) [bb(1) {event(2) < tau, status(2) = a} Qbar(2) (cal(F)^bold(1)_(event(2)))| history(1) ] | history(0)] ] 
$
Adding $zeta_1 (P)$, $zeta_2 (P)$, $zeta_3 (P)$, $zeta_4 (P)$, together, we find
    $
        sum_(j=1)^4 zeta_j (P) &= mean(P_(L(0))) [mean(P) [(bb(1) {event(1) < tau, status(1) = ell} + bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = 1})/(pi_1 (event(1), history(0)))) \
            &qquad times Qbar(1) (history(1))  | history(0)] ] 
    $ 
Similarly, we have that
$
    &mean(P) [bb(1) {event(1) < tau, status(1) = a} (bb(1) {treat(1) = a} )/(pi_1 (event(1), history(0))) Qbar(1) (history(1)) | history(0)] \
        &=mean(P) [bb(1) {event(1) < tau, status(1) = a} Qbar(1) (cal(F)^bold(1)_(event(1))) | history(0)],
$
so that
    $
        sum_(j=1)^4 zeta_j (P) &= mean(P_(L(0))) [mean(P) [bb(1) {event(1) < tau, status(1) = ell} Qbar(1) (history(1)) + bb(1) {event(1) < tau, status(1) = a} Qbar(1) (cal(F)^bold(1)_(event(1))) \
            &+ bb(1) {event(1) <= tau, status(1) = y} | history(0)] ]. 
$
Now, we finally see that
    $
        sum_(j=1)^4 zeta_j (P) + zeta_5 (P) = mean(P_(L(0))) [Qbar(0) (history(0))],
    $
    and we are done. 
]
Thus, regression techniques can be used to estimate the target parameter $Psi_tau (P)$.
Not only can it be used for the estimates of the target parameter,
but it turns that the terms $
    Qbar(0)$, $Qbar(1)$, and $Qbar(2)$, $Psi_tau (P)$,
as well as $pi_k (t, history(k-1))$ are precisely the terms
we encounter in the efficient influence function. Therefore, inference
can be obtained as part of the procedure
where we estimate $Qbar(0)$, $Qbar(1)$, and $Qbar(2)$ by considering a one-step estimator.
Furthermore, the resulting estimator will be doubly robust. 
We also give the ICE formula in case of censoring.
Let $Lambda_k^c (dif t | history(k-1))$ denote the cumulative cause-specific hazard function
for the censoring for the $k$'th event. Also,
let $Lambda^c (t)$ denote the compensator for
the censoring process with respect to the natural filtration
of all processes involved. 

#example[
    Let $S_((k))^c (event(k)- | history(k-1)) = product_(s in (event(k-1), event(k))) (1 - Lambda_k^c (dif s | history(k-1))) = product_(s in (event(k-1), event(k))) (1 - Lambda^c (dif s))$ denote the survival function for the censoring process.
    Defining,
    $
        &Z^a_3 = (bb(1) {event(3) <= tau}) / (S_((3))^c (event(3)- | history(2))), \
    &Qbar(2) (f_(t_2)) \
            &= mean(P) [Z^a_3 | history(2) = f_(t_2)], \ \
            &Z^a_2 = 1/ (S_((2))^c (event(1)- | history(1))) times (bb(1) {event(2) <= tau, status(2) = y} + bb(1) {event(2) < tau, status(2) = ell} Qbar(2) (history(2)) + \
                &qquad bb(1) {event(2) < tau, status(2) = a} Qbar(2) (cal(F)^bold(1)_(event(2)))) \
        
        &Qbar(1) (f_(t_1)) \
        &= mean(P) [Z_2^a | history(1) = f_(t_1)], \ \

            &Z^a_1 = 1/ (S_((1))^c (event(1)- | history(0))) times (bb(1) {event(1) <= tau, status(1) = y} + bb(1) {event(1) < tau, status(1) = ell} Qbar(1) (history(1)) + \
                &qquad bb(1) {event(1) < tau, status(1) = a} Qbar(1) (cal(F)^bold(1)_(event(1)))) \
        &Qbar(0) (f_0) \
        &= mean(P) [Z_1^a | history(0)=f_0],
$
and 
$
    cal(F)^bold(1)_(event(2)) &= (event(2), status(2), 1, covariate(2), event(1), status(1), treat(1), covariate(1), treat(0), covariate(0), "age"),\
    cal(F)^bold(1)_(event(1)) &= (event(1), status(1), 1, covariate(1), treat(0), covariate(0), "age"),
$
    which is the history where we set the _current_ treatment to 1.
Then, $Psi_tau (P) = mean(P_(L(0))) [Qbar(0) (history(0))]$,
    where $P_(L(0))$ is the distribution of the baseline confounders.
] <example:ice-censoring>

== Example usage of the Algorithm <section:example>

To help illustrate the algorithm, we present a simple example in @fig:longitudinaldataice in the case where $tau = 5$.
We start at $k=3$.
As in the rest of the paper, we suppose that the time horizon is $tau = 720$.
We apply the definitions given in @example:ice.

#outline-colorbox(
      title: [Iteration $k=3$],
        color: "blue",
        radius: 2pt,
    width: auto,
    centering: true,
)[
    Denote by $R_(3,tau) $ the set of people for which it is possible that may die as their
    third event before time $tau$, that is people with $event(2) < tau$ and $event(2) in {a, ell}$
    (otherwise the probability we are trying to determine is zero).
    We find that $R_(3,tau) = {6, 7}$.
    For each of these people find $Z^a_(3)$ and regress on $historycensored(2)$ to obtain a prediction function $hat(nu)_(2)$.
    In *R*, this can be done as follows via e.g., `glm` assuming the data is given as `data`:
    ```r        
    D_3 <- data[data$status_2 %in% c("a", "l") & data$time_2 < tau, ] ## data set that consists of ids from R_3
    data$Z_3 <- 1*(D_3$time_3 <= tau)
    fit <- glm(Z_3 ~ time_2+status_2+A_2+L_2+ time_1+status_1+A_1+L_1+A_0+L_0+age, data = D_3, family = "binomial") ## example; can use ML methods or in principle also include interactions
    hat_nu_2 <- function(data) {predict(fit, newdata=data, type = "response")}
    ```
          ]
#outline-colorbox(
        title: [Iteration $k=2$],
          color: "blue",
          radius: 2pt,
            width: auto,
            centering: true,
            )[

As in the case $k=3$, we find $R_(2,tau) = {3, 4, 6, 7}$.
- For $i=3$, we produce the altered history, where
                $cal(F)^1_(macron(T)_(2,i)) = (55,0, 1,1, 1,62, ell, 1, 1)$ to $hat(nu)_2$
                and find $hat(nu)_2 (cal(F)^1_(macron(T)_(2,i)))$.
                Based on this we calculate $hat(Z)^a_(2,i) = 1 times hat(nu)_2 (cal(F)^1_(macron(T)_(2,i)))$.
- For $i = 4$, we apply the actual history $cal(F)_(macron(T)_(2,4))$ to $hat(nu)_2$. Again,
  we calculate $hat(Z)^a_(2,4) = 1 times cal(F)_(macron(T)_(2,4))$.
- For $i=7$, similarly calculate $hat(Z)^a_(2,4) = 1 cal(F)_(macron(T)_(2,6))$.
- For $i=6$, we simply find $hat(Z)^a_(2,7) = 1$.
Regress the predicted values $hat(Z)^a_(2)$ on $history(1)$ to obtain a prediction function $hat(nu)_(1)$.
                In *R*, this can be done as follows via e.g., `lm` assuming the data is given as `data`:
                ```r
                D_2 <- data[data$status_1 %in% c("a", "l") & data$time_1 < tau, ] ## data set that consists of ids from R_2
                D_2a <- copy(data)
                D_2a[data$status_2 == "a", "treat_2"] <- 1 ## alter treat_2 to 1 for those with status_2 = a
                data$Z_2 <- 1*(D_2$time_2 <= tau & D_2$status_2 == "y") + 
                    1*(D_2$time_2 < tau & D_2$status_2 == "l") * hat_nu_2(D_2a) + 
                    1*(D_2$time_2 < tau & D_2$status_2 == "a") * hat_nu_2(D_2a)
                fit <- lm(Z_2 ~ time_1+status_1+A_1+L_1+A_0+L_0+age, data = D_2)
                hat_nu_1 <- function(data) {predict(fit, newdata=data, type = "response")}
                ```
            ]
#outline-colorbox(
        title: [Iteration $k=1$],
          color: "blue",
          radius: 2pt,
            width: auto,
            centering: true,
            )[

Same procedure as $k=2$. Note that we find $R_(1,tau) = {1, 2, 3, 4, 5, 6, 7}$.
            ]
#outline-colorbox(
        title: [Iteration $k=0$],
          color: "blue",
          radius: 2pt,
            width: auto,
            centering: true,
            )[

We get the estimate $hat(Psi)_n = 1/7 sum_(i=1)^7 hat(nu)_(0) (1, 0, "sex"_i (0))$ for $n=7$,
where we obtained $hat(nu)_(0)$ from $k=1$.
            ]

#figure(table(
    columns: (auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto, auto),
    table.header(
        [id], [age],
        [$covariate(1)$], [$treat(1)$], [$event(1)$], [$status(1)$],
        [$covariate(2)$], [$treat(2)$], [$event(2)$], [$status(2)$],
        [$event(3)$], [$status(3)$]
    ),
    [1], [60], [0], [1], [745], [$a$], [Ø], [Ø], [770], [$y$], [$oo$], [Ø],
    [2], [50], [Ø], [Ø], [140], [$y$], [Ø], [Ø], [$oo$], [Ø], [$oo$], [Ø],
    [3], [55], [1], [1], [62], [$ell$], [1], [0], [850], [$a$], [$870$], [$y$],
    [4], [46], [1], [1], [70], [$ell$], [1], [1], [170], [$a$], [$182$], [$y$],
    [5], [67], [Ø], [Ø], [60], [$y$], [Ø], [Ø], [$oo$], [Ø], [$oo$], [Ø],
    [6], [52], [1], [1], [120], [$ell$], [Ø], [Ø], [175], [$y$], [$oo$], [Ø],
    [7], [56], [0], [0], [40], [$a$], [1], [0], [80], [$ell$], [$645$], [$y$],

                ),
                caption: [
                    Example data for illustration of the ICE algorithm. $covariate(0)$ and $treat(0)$ are not shown as they are constant. 
                ])<fig:longitudinaldataice>

= Simulation study <sec:simulation-study>

Consider the following example coefficients for the simulation mechanism, corresponding to a simulation mechanism,
which is compatible with the time-varying Cox model, e.g., $lambda^y := lambda_1^y = lambda_2^y = lambda_3^y$ (see e.g., @sec:intensities). We vary the treatment
effect on the outcome $beta_(k, A)^y$, corresponding to $beta_(k, A)^y > 0$, $beta_(k, A)^y = 0$, and $beta_(k, A)^y < 0$,
and the effect of a stroke on the outcome $beta_(k, L)^y$, corresponding to $beta_(k, L)^y > 0$, $beta_(k, L)^y = 0$, and $beta_(k, L)^y < 0$.
We also vary the effect of a stroke on the treatment propensity $alpha_(k, "L")$
and the effect of treatment on stroke $beta_(k, A)^ell$.
The overall goal is to assess the impact of baseline and time-varying confounding
and if our method is a viable method of estimating the target parameter $Psi_tau (P)$.
We compare our method to the naive method using the Cox model, which
treats deviation from protocol as censoring. Furthermore,
we discretize time into 8 intervals (@sec:discretizing-time),
enabling comparisons with Longitudinal Targeted Maximum Likelihood Estimation (LTMLE) @ltmle.
We consider both the debiased ICE estimator and the simple ICE estimator;
the difference between them being that we add the efficient influence function
to the first, which allows us to obtain doubly robust inference.
Only the first of these are used to obtain standard errors.
Finally, we also compare with a continuous-time inverse probability weighting
estimator which cannot be misspecified.

Additionally, we vary sample size $n in {100, 2000, 500, 1000}$.
In all cases, we fix $n=1000$.

We thus consider three overall scenarios:
- *No baseline and time-varying confounding*.
- *No time-varying confounding but baseline confounding*.
- *Time-varying confounding*
- *Strong confounding*.

We highlight the interpretation of the most important parameters in the simulation mechanism:
- $alpha_(k, "age")$: If positive: You will more likely be treated if you are older.
- $alpha_(k, "L")$: If negative: You will be less likely to be treated if you have had a stroke.
- $beta_(k,"age")^x$: If positive: The risk of having a stroke or primary event increases with age.
- $beta_(k, A)^ell$: If negative: The risk of having a stroke is lower if you are treated.
- $beta_(k, L)^y$: If positive: The risk of having a primary event is higher if you have had a stroke.

Proposed values for the parameters are shown in the table below.
Each value is varied, holding the others fixed.
The values with bold font correspond to the values used
when fixed. The corresponding cases
corresponding to no effect of baseline confounders
are marked with an overline, and the cases corresponding to no effect of time-varying confounders
are marked with an underline.

#pagebreak()

#align(center, [
#table(
  columns: ( auto, auto),
  inset: 10pt,
  align: horizon,
  table.header(
    [*Parameters*], [*Values*],
  ),
    [$alpha_(k 0)$], [0.3],
    [$alpha_(k, "age")$], [0.02],
    [$alpha_(k, "L")$], [*-0.2*, #overline[0], 0.2],
    [$beta^y_(k, "age")$], [0.025],
    [$beta^ell_(k, "age")$], [0.015],
    [$beta^y_(k, A)$], [*-0.3*, #underline[0], 0.3],
    [$beta^ell_(k, A)$], [*-0.2*, #underline[0], 0.2],
    [$beta^y_(k, "L")$], [-0.5, #overline([0]), *0.5*],
    [$lambda_k^y$], [0.0001],
    [$lambda_k^ell$], [0.001],
    [$gamma_"age"$], [0],
    [$gamma_0$], [0.005]
)])

Strong confounding is considered in the following table
in two different simulation settings. 
#align(center, [
#table(
  columns: ( auto, auto),
  inset: 10pt,
  align: horizon,
  table.header(
    [*Parameters*], [*Values*],
  ),
    [$alpha_(k 0)$], [0.3],
    [$alpha_(k, "age")$], [0.02],
    [$alpha_(k, "L")$], [-0.6, 0.6],
    [$beta^y_(k, "age")$], [0.025],
    [$beta^ell_(k, "age")$], [0.015],
    [$beta^y_(k, A)$], [-0.8, 0.8],
    [$beta^ell_(k, A)$], [-0.2],
    [$beta^y_(k, "L")$], [1],
    [$lambda_k^y$], [0.0001],
    [$lambda_k^ell$], [0.001],
    [$gamma_"age"$], [0],
    [$gamma_0$], [0.005]
)])

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
    O = ("age", treat(0), covariate(0), Y_1, L_1, A_1, dots, Y_(K-1), L_(K-1), A_(K-1), Y_K)
$

== Nuisance parameter modeling

To apply our debiased ICE estimator in the uncensored situation, we need to estimate
two types of nuisance parameters:
1. The treatment propensity $pi_k (t, history(k-1))$ for each $k$.
2. The conditional counterfactual probabilities $Qbar(k)$ for each $k$.

For the treatment propensities, we consider correctly specified models
using logistic regression.

For modeling the conditional counterfactual probabilities $Qbar(k)$,
we a generalized linear model (GLM) with the option `family = quasibinomial()`,
using no interactions in the history, as was discussed in @section:example.

For the LTMLE procedure, we use an undersmoothed LASSO (reference?) estimator.

== Censoring
We consider a simulation involving _completely_ independent censoring.
Concretely, the censoring variable is simply generated as $C tilde "Exp"(lambda_c)$.
The processes under considerations are then observed up to this censoring time.
We vary $lambda_c in {0.0002,0.0005,0.0008}$.
The overall purpose is to determine:
1. If the ICE algorithm can be used to estimate the target parameter $Psi_tau (P)$ in the case of censoring.
2. What model should be used to estimate the conditional counterfactual probabilities $Qbar(k)$?
3. Figure out whether or not we need also to debias the _so-called_ censoring martingale.

Here, we consider a linear model, 
   the scaled quasibinomial `glm` (this means that we divide with the largest value of $hat(Z)^k_a$
   in the sample so that it is scaled down to $[0, 1]$; afterwards the predictions are rescaled with the largest value), a tweedie `glm` (the pseudo-outcomes $Z_k^a$ may appear
   marginally as a mixture of a continuous random variable and a point mass at 0)
 as estimators of the conditional counterfactual probabilities $Qbar(k)$.

We consider only two parameter settings for the censoring martingale
as outlined below.
1.

#align(center, [
#table(
  columns: ( auto, auto),
  inset: 10pt,
  align: horizon,
  table.header(
    [*Parameters*], [*Values*],
  ),
    [$alpha_(k 0)$], [0.3],
    [$alpha_(k, "age")$], [0.02],
    [$alpha_(k, "L")$], [0, -0.2],
    [$beta^y_(k, "age")$], [0.025],
    [$beta^ell_(k, "age")$], [0.015],
    [$beta^y_(k, A)$], [0, -0.3],
    [$beta^ell_(k, A)$], [-0.2],
    [$beta^y_(k, "L")$], [0, 0.5],
    [$lambda_k^y$], [0.0001],
    [$lambda_k^ell$], [0.001],
    [$gamma_"age"$], [0],
    [$gamma_0$], [0.005]
)])

= Results
Here, the results are presented in a fairly unstructured format.
In the tables, we report the mean squared error (MSE),
mean bias, standard deviation of the estimates, and the mean of the estimated standard error,
as well as coverage of 95% confidence intervals.

Overall conclusions for the uncensored case:
1. The debiased ICE-IPCW estimator works well in all cases considered 
   with respect to bias. Moreover, it is unbiased in cases with
   substantial time-varying confounding and performs better than 
   both the naive Cox model and the LTMLE estimator.
2. Standard errors are generally good, but appear less unbiased.
   Is this due to misspecification of the nuisance parameters $Qbar(k)$?
3. LTMLE standard errors are generally a little bit smaller 
   than the debiased ICE-IPCW standard errors.
4. In the case with no confounding and $beta_A^y =0.3$, 
   no method appears to be unbiased. Some explanations: Either the simulation
   mechanism is too extreme or the prevalence of the event is too low.

Overall conclusions for the censored case:
1.  All choices of $lambda^c$ and all choices of nuisance parameter models seem
    to give unbiased estimates. 
2. Standard errors appear to be conservative. Overall, the standard errors for
   the tweedie model appear to be slightly higher.
3. The linear model appears to give the most unstable estimates.

== Tables

=== Uncensored

==== No confounding
#let results_table_no_confounding = csv("tables/results_table_no_confounding.csv")
#let _ = results_table_no_confounding.remove(0)

#table(
    columns: results_table_no_confounding.at(0).len(),
    //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
    [$beta^y_A$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd(Est)*], [*Mean($hat("SE")$)*],
  ..results_table_no_confounding.flatten(),
)

==== No time-varying confounding
#let results_table_no_time_confounding = csv("tables/results_table_no_time_confounding.csv")
#let _ = results_table_no_time_confounding.remove(0)

#table(
        columns: results_table_no_time_confounding.at(0).len(),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$beta^y_A$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd(Est)*], [*Mean($hat("SE")$)*],
          ..results_table_no_time_confounding.flatten(),
        )

==== Strong time-varying confounding
#let results_table_strong_time_confounding = csv("tables/results_table_strong_time_confounding.csv")
#let _ = results_table_strong_time_confounding.remove(0)

#table(
        columns: results_table_strong_time_confounding.at(0).len(),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$beta^y_A$], [$alpha_L$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd(Est)*], [*Mean($hat("SE")$)*],
          ..results_table_strong_time_confounding.flatten(),
)

==== Varying effects (A on Y, L on Y, A on L, L on A)
#let results_table_vary_effect_A_on_Y = csv("tables/results_table_vary_effect_A_on_Y.csv")
#let _ = results_table_vary_effect_A_on_Y.remove(0)

#table(
        columns: results_table_vary_effect_A_on_Y.at(0).len(),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$beta^y_A$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd(Est)*], [*Mean($hat("SE")$)*],
          ..results_table_vary_effect_A_on_Y.flatten(),
)

#let results_table_vary_effect_L_on_Y = csv("tables/results_table_vary_effect_L_on_Y.csv")
#let _ = results_table_vary_effect_L_on_Y.remove(0)

#table(
        columns: results_table_vary_effect_L_on_Y.at(0).len(),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$beta^y_L$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd(Est)*], [*Mean($hat("SE")$)*],
          ..results_table_vary_effect_L_on_Y.flatten(),
)

#let results_table_vary_effect_A_on_L = csv("tables/results_table_vary_effect_A_on_L.csv")
#let _ = results_table_vary_effect_A_on_L.remove(0)

#table(
        columns: results_table_vary_effect_A_on_L.at(0).len(),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$beta^L_A$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd(Est)*], [*Mean($hat("SE")$)*],
          ..results_table_vary_effect_A_on_L.flatten(),
)

#let results_table_vary_effect_L_on_A = csv("tables/results_table_vary_effect_L_on_A.csv")
#let _ = results_table_vary_effect_L_on_A.remove(0)

#table(
        columns: results_table_vary_effect_L_on_A.at(0).len(),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$alpha_L$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd(Est)*], [*Mean($hat("SE")$)*],
          ..results_table_vary_effect_L_on_A.flatten(),
)

#let results_table_sample_size = csv("tables/results_table_sample_size.csv")
#let _ = results_table_sample_size.remove(0)

#table(
        columns: results_table_sample_size.at(0).len(),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
        [$n$], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd(Est)*], [*Mean($hat("SE")$)*],
          ..results_table_sample_size.flatten(),
)

=== Censored

#let results_table_censored = csv("tables/results_table_censored.csv")
#let _ = results_table_censored.remove(0)

#table(
        columns: results_table_censored.at(0).len(),
        //[$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$beta^L_A$], [$beta^Y_"age"$], [$alpha_"age"$], [$lambda^y$], [*Est.*], [*Cov.*],
    [$beta^y_A$], [$beta^y_L$], [$alpha_L$], [$lambda_c$], [*Model type*], [*Estimator*], [*Coverage*],
    [*MSE*], [*Bias*], [*sd(Est)*], [*Mean($hat("SE")$)*],
          ..results_table_censored.flatten(),
)

== Boxplots

=== Uncensored

==== No confounding
#figure(
    image("plots/boxplot_results_no_confounding.svg"),
        caption: [
                Boxplots of the results for the case without time confounding.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("plots/se_boxplot_results_no_confounding.svg"),
        caption: [
                Boxplots of the standard errors for the case without time confounding.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

==== No time-varying confounding
#figure(
    image("plots/boxplot_results_no_time_confounding.svg"),
        caption: [
                Boxplots of the results for the case without time confounding.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("plots/se_boxplot_results_no_time_confounding.svg"),
        caption: [
                Boxplots of the standard errors for the case without time confounding.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

==== Strong time-varying confounding
#figure(
    image("plots/boxplot_results_strong_time_confounding.svg"),
        caption: [
                Boxplots of the results for the case with strong time confounding.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("plots/se_boxplot_results_strong_time_confounding.svg"),
        caption: [
                Boxplots of the standard errors for the case with strong time confounding.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

==== Varying effects (A on Y, L on Y, A on L, L on A)
#figure(
    image("plots/boxplot_results_vary_effect_A_on_Y.svg"),
        caption: [
                Boxplots of the results for the case with varying effect of $A$ on $Y$.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("plots/se_boxplot_results_vary_effect_A_on_Y.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying effect of $A$ on $Y$.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

#figure(
    image("plots/boxplot_results_vary_effect_L_on_Y.svg"),
        caption: [
                Boxplots of the results for the case with varying effect of $L$ on $Y$.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("plots/se_boxplot_results_vary_effect_L_on_Y.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying effect of $L$ on $Y$.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

#figure(
    image("plots/boxplot_results_vary_effect_A_on_L.svg"),
        caption: [
                Boxplots of the results for the case with varying effect of $A$ on $L$.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("plots/se_boxplot_results_vary_effect_A_on_L.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying effect of $A$ on $L$.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

#figure(
    image("plots/boxplot_results_vary_effect_L_on_A.svg"),
        caption: [
                Boxplots of the results for the case with varying effect of $L$ on $A$.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("plots/se_boxplot_results_vary_effect_L_on_A.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying effect of $L$ on $A$.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

#figure(
    image("plots/boxplot_results_sample_size.svg"),
        caption: [
                Boxplots of the results for the case with varying sample size.
                The lines indicates the true value of the parameter.
        ],
)

#figure(
    image("plots/se_boxplot_results_sample_size.svg"),
        caption: [
                Boxplots of the standard errors for the case with varying sample size.
            The red line indicates the empirical standard error of the estimates for each estimator.
        ],
)

#figure(
    image("plots/boxplot_results_censored.svg"),
        caption: [
                Boxplots of the results for the case with censoring.
            Different degrees of censoring are considered as well different model types for the pseudo-outcomes.
            Only the debiased ICE-IPCW estimator is shown.
        ],
)

#figure(
        image("plots/se_boxplot_results_censored.svg"),
                caption: [
                        Boxplots of the standard errors for the case with censoring.
                The red line indicates the empirical standard error of the estimates for each estimator.
                ])

#figure(
    image("plots/boxplot_results_censored_ice_ipcw.svg"),
        caption: [
            Boxplots of the results for the case with censoring.
            Different degrees of censoring are considered as well different model types for the pseudo-outcomes.
            Here, the (not debiased) ICE-IPCW estimator is shown.
        ],
)

= Extensions <sec:extensions>
Let $T^ell$ be the time since the last stroke (i.e., 0 if stroke occurred as the previous event and $event(2)-event(1)$ if it happened as the first event).
Then, we might consider
$
    S_((3))^y tilde "Exp"(lambda^y_3 exp(beta^y_(3,"age") "age" + beta^y_(3, A) treat(2) + beta^y_(3, L) covariate(2) + beta^y_(3, T^ell) T^ell)),
$
or we might consider a model in which the baseline hazard is not constant.
It also might be easier to state a realistic model in terms of the intensities directly,
in which case, we can then "transform" to the interevent scale. For example, a realistic intensity for the primary event,
$
    lambda^y (t) &= lambda_0^y (t) exp(beta^y_("age") "age") exp(beta_L^y exp(beta^(y *)_L (t-T^ell)) L(t-) + beta_A^y  exp(beta^(y *)_A (t-T^a)) (1-A(t-)) \
        &+ beta^y_Z bb(1) {event(2) < t} bb(1) {status(1)=a} bb(1) {status(2)=ell}) bb(1) {t <= T^y}
$
Here $T^a$ denotes the time to the last treatment. 
Note that each term is zero if the corresponding event has not happened yet, so we do not condition on the future. 
Here, we can let each coefficient depend on event number, but for simplicity of notation, we do not do so.
The last term corresponds to there being an effect of the order in which the events happened
after two events. 
This is one way to include longe range dependencies.
Simulating from this model is significantly more complicated, because we have to rely on numeric integration.
Otherwise, there is the possibility of using Ogata's thinning algorithm @ogata1981lewis.
It is likely here that the LTMLE algorithm considered would be even more biased
as it cannot take into account the timing of the events. 

More generally, let $cumhazard(k, x, t)$ denote the cumulative hazard function for the $k$'th event of type $x$ at time $t$
conditional on the history $history(k-1)$.
The cumulative hazard-cause specific hazard of $S_((k))$ of the $k$'th event type $x$ is given by
$
    [tauend - event(k-1), 0) in.rev t mapsto cumhazard(k, x, t + event(k-1)) - Lambda^x_k (event(k-1), history(k-2))
$
If we suppose for simplicity that $cumhazard(k, x, t)$ is invertible on $(event(k-1), tauend]$
with say inverse $Lambda^(-1,x)_k (dot,history(k-1))$
letting $E tilde "Exp"(1)$ be an exponential random variable with mean 1,
we can simulate $S_((k))^x$ as follows
$
    S_((k))^x = Lambda^(-1,x)_k (E + Lambda^x_k (event(k-1), history(k-2)),history(k-2))  - event(k-1),
$
This can be seen by using the fact that if $Lambda$ is a cumulative hazard function for the random variable $T$,
then $Lambda^(-1) (E)$ is a random variable with the same distribution as $T$.

= Intensities <sec:intensities>

It is illustrative to compare the simulation mechanism with a
model for the intensities. Furthermore, we argue that
observations from a counterfactual distribution can be simulated
by setting $treat(k) = 1$ for each $k = 1, dots, K$.

First, let us define the counting processes as
$
    N^y (t) &= sum_(k=1)^3 bb(1) {status(k) = y, event(k) <= t}, \
    N^ell (t) &= sum_(k=1)^2 bb(1) {status(k) = ell, event(k) <= t}, \
    N^(a 1) (t) &= sum_(k=1)^2 bb(1) {status(k) = a, event(k) <= t, treat(k) = 1}, \
        N^(a 0) (t) &= sum_(k=1)^2 bb(1) {status(k) = a, event(k) <= t, treat(k) = 0}.
$
Using Theorem II.7.1 of #cite(<andersenStatisticalModelsBased1993>, form: "prose"),
we find that $N^y$ has the compensator
$
    Lambda^y (t) &= integral_0^t sum_(k=1)^3 bb(1) {event(k-1) < s <= event(k)} lambda_k^y exp(beta^y_(k, "age") "age" + beta^y_(k, A) treat(k-1) + beta^y_(k, L) covariate(k-1)) dif s 
$
If $lambda_1^y = lambda_2^y = lambda_3^y$, we can write the intensity as
$
    lambda^y (t) &= lambda_1^y \
        &exp(beta^y_(k, "age") "age") exp( beta^y_(1, A) A(t-) + (beta^y_(2, A)-beta^y_(1, A)) bb(1) {event(1) < t <= event(2)}  A(t-) \
            &qquad + (beta^y_(3, A)-beta^y_(2, A)) bb(1) {event(2) < t <= event(3)}  A(t-) + beta^y_(1, "L") L(t-) \
            &qquad + (beta^y_(2, "L")-beta^y_(1, "L")) bb(1) {event(1) < t <= event(2)} L(t-) \
            &qquad + (beta^y_(3, "L")-beta^y_(2, "L")) bb(1) {event(2) < t <= event(3)} L(t-)) bb(1) {t <= event(3) and tauend} \
$
which shows that the model is compatible with the time-varying Cox model.
We may find a similar expression for $N^ell$.

Let $pi_t (a) = sum_(k=1)^2 bb(1) {event(k-1) < t <= event(k)} "expit" (alpha_(k 0) + alpha_(k, "age") "age" + alpha_(k, "L") covariate(k-1))$
and $pi_t^* (a) = sum_(k=1)^2 bb(1) {event(k-1) < t <= event(k)} bb(1) {a= 1}$.
Let $lambda^a$ be defined analogously to $lambda^y$, then we find
via Theorem II.7.1 of #cite(<andersenStatisticalModelsBased1993>, form: "prose"),
that $N^(a 1)$ and $N^(a 0)$ have the compensators
$
        Lambda^(a 1) (t) &= integral_0^t pi_s (1) lambda^a (s) dif s, \
        Lambda^(a 0) (t) &= integral_0^t pi_s (0) lambda^a (s) dif s.
$
respectively. Simulating from the interventional mechanism corresponds to
having the compensators
$
    Lambda^(a 1) (t) &= integral_0^t pi_s^* (1) lambda^a (s) dif s, \
        Lambda^(a 0) (t) &= integral_0^t pi_s^* (0) lambda^a (s) dif s.
$
with the other compensators unchanged, which is the continuous time $g$-formula. 

#bibliography("ref.bib", style: "apa")

