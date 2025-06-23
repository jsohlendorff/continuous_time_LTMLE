#import "definitions.typ": *

= Simulating longitudinal data for time-to-event analysis in continuous time

We simulate a cohort of patients who initiate treatment at time $t = 0$, denoted by $A(0) = 1$
and who are initially stroke-free, $L(0) = 0$.
All individuals are followed for up to $tauend = 730 "days"$ or until death.
Initially, we do not consider censoring or competing events. 
During follow-up, patients may experience (at most) one stroke, stop treatment (irreversibly), and die,
that is $N^x (t) <= 1$ for $x = a, ell, y$.
With these assumptions $K=2$ in the main note (at most two non-terminal events).
The primary outcome is the _risk of death within 2 years_.

As in the note, we assume that a treatment event and a covariate event cannot happen at the same time,
which is not a significant limitation.
Our observations consist of
$
    O = (event(3), status(3), treat(2), covariate(2), event(2), status(2), treat(1), covariate(1), event(1), status(1), treat(0), covariate(0), "age"),
$
where $event(k)$ is the time of the $k$'th event, $status(k) in {ell, a, y, c}$ (stroke, visit, death, censored),
$treat(k)$ is the treatment status at time $event(k)$, and $covariate(k)$ is the value of the covariate at time $event(k)$.
We reserve $c$ for administrative censoring, corresponding to the event happening after the end of the study period, $tauend$.
Note that we let $event(k) = oo$ if the $k$'th event cannot happen (because the previous event was a terminal event or the end of the study period was reached).

Then, we generate the baseline variables as follows
$
    &"age" tilde "Unif"(40,90), \
        &L = 0, \
        & treat(0) = 1,
$

Now we describe the simulation mechanism corresponding to the first event that can happen.
To allow for administrative censoring, let $T_((1))^c = 2$.
We define $T_((1))^a$ such that the patient can be expected
to go to the doctor within the first year,
if the two other events have not occurred first.
Let Exp($lambda$) denote the exponential distribution with rate $lambda >= 0$.
We let $lambda = 0$ correspond to the case that the event cannot happen, i.e., $T_((1))^x = oo$.
As the first event, we draw
$
    &T_((1))^x  tilde "Exp"(lambda^x_0 exp(beta^x_(0,"age") "age")), qquad x = ell, y \
        &T_((1))^a tilde 1 + cal(N)(0, delta) \
        &status(1) = "argmin"_(x = a, ell, y, c) T_((1))^x \
        &event(1) = T_((1))^status(1) \
        &treat(1) | event(1) = t, "age" = x cases(tilde "Bernoulli(expit"(alpha_(00) + alpha_(0, "age") x) "if" status(1) = a, 1 "otherwise") \
        &covariate(1) = 1, \
$
Note that we simulate from a "competing event setup" by defining latent variables $T_((1))^x$ for each possible event type $x$.

We now describe the second event that can happen.
If the first event was a terminal event -- either outcome or administrative censoring --
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
    &S_((2))^ell tilde "Exp"(lambda^ell_1 exp(beta^ell_(1,"age") "age" + beta^ell_(1, A) (1-treat(1))) bb(1) {status(1) = a}) \
        &S_((2))^y tilde "Exp"(lambda^y_1 exp(beta^y_(1,"age") "age" + beta^y_(1, A) (1-treat(1)) + beta^ell_(1, L) covariate(1))) \ 
            &S_((2))^c = 2 - event(1) \
        &S_((2))^a tilde "Exp"(gamma_0 exp(gamma_"age" "age") bb(1) {status(1) =ell}) \
            &status(2) = "argmin"_(x = a, ell, y, c) S_((2))^x \
            &event(2) = event(1) + S_((2))^status(2) \
        &treat(2) | event(2) = t, "age" = x, treat(1) = a_1, covariate(1) = l_1 \
        &qquad =cases(tilde "Bernoulli(expit"(alpha_(10) + alpha_(1, "age") x) "if" status(2) = a, 1 "otherwise") \
        &covariate(2) = 1. \
$
In the following, we assumed that the previous event times have no influence on anything,
only the "marks". However, this may be unrealistic, as the effect of a stroke on mortality may naturally decrease over time.

Finally, we let $event(3) = S_((3)) + event(2)$ denote the time of the third event,
if it can happen.
We define the time $S_((3))$ as follows:
$
    S_((3))^y tilde "Exp"(lambda^y_2 exp(beta^y_(2,"age") "age" + beta^y_(2, A) (1-treat(2)) + beta^y_(2, L) covariate(2))) \
    S_((3))^c = 2 - event(2) \
    status(3) = "argmin"_(x = y, c) S_((3))^x \
    event(3) = event(2) + S_((3))^status(3).
$
Here, we furthermore make the assumption that
it does not matter whether the patient had a stroke first
and then visited the doctor, or visited the doctor first and then had a stroke.

When the static intervention is applied, we put $treat(k) = 1$ for each $k = 1, dots, K$.
It is not too difficult to see that the likelihood factorizes as in #cite(<rytgaardContinuoustimeTargetedMinimum2022>, form: "prose")
corresponding to the intervention that we are interested in (see e.g., Theorem II.7.1 of #cite(<andersenStatisticalModelsBased1993>, form: "prose")).

//\eqn{Δ(k) = \arg\min_x Sₓ(k)}
//\eqn{T(k) = T(k-1) + S_{Δ(k)}(k)}

= Plain Language Summary (for Clinical Audience)

We simulate patients who all begin treatment and are initially healthy.
Over two years, they may have a stroke, stop treatment (only at doctor visits), or die.
A routine doctor visit is scheduled about a year after treatment begins,
unless a stroke happens first, in which case a visit is likely to occur soon after.
Doctors are less likely to stop treatment after a stroke.
The chance of dying depends on whether the patient has had a stroke and whether they are still on treatment.

#bibliography("ref.bib", style: "apa")
