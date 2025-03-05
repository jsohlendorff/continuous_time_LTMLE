#import "@preview/fletcher:0.5.1": node, edge, diagram
// #import "template.typ": conf
#import "template/definitions.typ"
#import "@preview/arkheion:0.1.0": arkheion, arkheion-appendices
#import "@preview/cetz:0.3.1"
#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#set cite(form: "prose")
// Color references red
#show  ref: it => {text(fill: maroon)[#it]}
#let mapsto = $arrow.bar$
#let scr(it) = text(
    features: ("ss01",),
    box($cal(it)$),
)

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let proof = thmproof("proof", "Proof")

#show: arkheion.with(
    title: "A note on the L2-convergence rates of derivatives",
    authors: (
        (name: "Johan Sebastian Ohlendorff", email: "johan.ohlendorff@sund.ku.dk", affiliation: "University of Copenhagen"),
    ),
    abstract: [In this brief note, ...
    ]
    // Insert your abstract after the colon, wrapped in brackets.
    // Example: `abstract: [This is my abstract...]`
)

#show: thmrules.with(qed-symbol: $square$)

= Main section

Let the $L_2 (nu)$-norm of a function $f in L_2 (nu)$ be defined as
$
norm(f)_nu = sqrt(integral f^2 d nu).
$
Consider a sequence of estimators $hat(P)_n (t | x)$ of $P (t | x)$ which are defined on $[0, tau]$.
We assume that $hat(P)_n (0 | x) = P (0 | x) = 0$.
We let $mu_0$ denote an appropriate measure for the covariates $x$.
These are assumed to have the $L_2 (mu_0)$-convergence rate $n^(-1/4-epsilon)$ for Lebesgue almost all $t in [0, tau]$
for $epsilon > 1/12$. This corresponds to a convergence rate of slightly better than $n^(-1/3)$.
//, where $mu_0$ is the Lebesgue measure on $[0, tau]$.
We are interested in constructing an estimator $p (t | x) = P' (t | x)$ of the derivative of $P (t | x)$
which also has the $L_2 (mu_0 times.circle m)$-convergence rate $n^(-1/4)$,
where $m$ is the Lebesgue measure on $[0, tau]$.
The precise statement is given in @thm:main.
This is useful if one wishes to obtain convergence rates for a hazard function which one has not explicitly considered,
but only the cumulative hazard function, such as in a Cox regression.

#theorem[
    Let $hat(P)_n (t | x)$ be a sequence of estimators of $P (t | x)$ defined on $[0, tau]$ fulfilling that $hat(P)_n (0 | x) = P (0 | x) = 0$.
    Suppose that $P (t | x) in C^2 ([0, tau])$ for $mu_0$-almost all $x$ and that there exists a constant $K>0 $ such that
    $p '(t | x) <= K$ for $mu_0$-almost all $x$ and $t in [0, tau]$.
    If $ norm(hat(P)_n (t | dot) - P (t | dot))_(mu_0) = o_P (n^(-1/4-epsilon))$ for Lebesgue almost all $t in [0, tau]$ for $epsilon > 1/12$,    then there exists an estimator $hat(p)_n (t | x)$ of $p (t | x) = P' (t | x)$ such that
    $
        norm(hat(p)_n - p)_(mu_0 times.circle m) = o_P (n^(-1/4)).
    $
    The estimator $hat(p)_n (t | x)$ fulfills on a grid $0 = t_1 < ... < t_(K_n) = tau$ with some mesh $b(n) = max_(1 <= k <= K_n) (t_k - t_(k-1)) -> 0$ as $n -> oo$
    and $K_n -> oo$ as $n -> oo$ determined by $epsilon$ such
    $
        integral_0^(t_k) hat(p)_n (s | x) d s  = hat(P)_n (t_k | x).
    $
]<thm:main>
#proof[
    Consider a partition $0 = t_1 < ... < t_(K_n) = t$ of $[0, t]$ with mesh $b(K_n) = max_(1 <= k <= K_n) (t_k - t_(k-1))$.
    Choose $x_1 > 0$ and $x_2 < 0$ such that $0 < x_1 < 3/4 epsilon - 1/16$ and $2 (x_1 - epsilon) < x_2 < -2/3 epsilon - 1/6 < 0$.
    Here, we will let $K_n = round(n^(x_1)))$ and $b(K_n) = round(n^(x_2))$.
    Then $K_n -> oo$ as $n -> oo$ because $epsilon > 1/12$ and $b(K_n) -> 0$ as $n -> oo$ because $epsilon > 0$.
    We will show the theorem by constructing an explicit estimator $hat(p)_n (t | x)$ by approximating the derivative via a secant.
    Let
    $
        hat(p)_n (t | x) = sum_(k=1)^(K_n) bb(1) {t in (t_(k), t_(k+1)]} (hat(P)_n (t_(k+1) | x) - hat(P)_n (t_k | x)) / (t_(k+1) - t_k)
    $
    Then evidently, we have
    $
        integral_0^(t_k) hat(p)_n (s | x) d s = sum_(j=1)^(k-1) (hat(P)_n (t_(k+1) | x) - hat(P)_n (t_k | x)) / (t_(k+1) - t_k)  (t_(k+1) - t_k) = hat(P)_n (t_k | x).
    $
    Furthermore, let
    $
        tilde(p)_n (t | x) = sum_(k=1)^(K_n) bb(1) {t in (t_(k), t_(k+1)]} (P (t_(k+1) | x) - P (t_k | x)) / (t_(k+1) - t_k).
    $
    By the triangle inequality, we have
    $
        norm(hat(p)_n - p)_(mu_0 times.circle m) <= norm(hat(p)_n - tilde(p)_n)_(mu_0 times.circle m) + norm(tilde(p)_n - p)_(mu_0 times.circle m).
    $
    We start with the first term on the right-hand side.
    $
        norm(hat(p)_n - tilde(p)_n)_(mu_0 times.circle m) &= norm(sum_(k=1)^(K_n) bb(1) {dot in (t_(k), t_(k+1)]} ((hat(P)_n (t_(k+1) | dot) - P (t_(k+1) | dot)) - (hat(P)_n (t_(k) | dot) - P (t_(k) | dot)) ) / (t_(k+1) - t_k) )_(mu_0 times.circle m) \
            &<= sum_(k=1)^(K_n) norm(bb(1) {dot in (t_(k), t_(k+1)]} (hat(P)_n (t_(k+1) | dot) - P (t_(k+1) | dot) - (hat(P)_n (t_(k) | dot) - P (t_(k) | dot))) / (t_(k+1) - t_k) )_(mu_0 times.circle m) \
            &<= sum_(k=1)^(K_n) 1/(sqrt(t_(k+1) - t_k)) (norm(hat(P)_n (t_(k+1) | dot) - P (t_(k+1) | dot))_(mu_0) + norm(hat(P)_n (t_(k) | dot) - P (t_(k) | dot))_(mu_0)) \
            &= o (n^(x_1 - 1/2 x_2)) o_P (n^(-1/4-epsilon)) = o_P (n^(epsilon-1/4-epsilon)) =  o_P (n^(-1/4)).
    $
    There exists by the mean value theorem a $xi_(k,x) in (t_(k), t_(k+1))$ such that $(P (t_(k+1) | x) - P (t_k | x)) / (t_(k+1) - t_k) = p (xi_(k,x) | x)$
    for $mu_0$-almost all $x$. Furthermore, there exists also a $xi'_(k,t,x)$ between $t$ and $xi_(k,x)$ such that
    $ p(t | x) - p (xi_(k,x) | x) = (t - xi_(k,x)) p' (xi'_(k,t,x) | x)$.
    This implies that we can bound the second term on the right-hand side as
    $
        norm( tilde(p)_n - p)_(mu_0 times.circle m) &= norm( sum_(k=1)^(K_n) bb(1) {dot in (t_(k), t_(k+1)]} p (xi_(k, dot) | dot)- p (dot | dot) )_(mu_0 times.circle m) \
            &= norm( sum_(k=1)^(K_n) bb(1) {dot in (t_(k), t_(k+1)]} (p (xi_(k, dot) | dot)- p (dot | dot)) )_(mu_0 times.circle m) \
            &= norm( sum_(k=1)^(K_n) bb(1) {dot in (t_(k), t_(k+1)]} (dot - xi_(k, dot)) p' (xi'_(k, dot, dot) | dot) )_(mu_0 times.circle m) \
            &<= K sum_(k=1)^(K_n) (t_(k+1) - t_k) sqrt(t_(k+1) - t_k) \
            &= K sum_(k=1)^(K_n) (b(k))^(3/2) = o (n^(x_1 + 3/2 x_2)) = o (n^(-1/4)).
    $
    so that we have
        $
                norm(hat(p)_n - p)_(mu_0 times.circle m) = o_P (n^(-1/4)).
        $
]

