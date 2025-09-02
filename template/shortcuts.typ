// event definitions
#let event(ind) = {
  if ind == [0] or ind == 0 [
    $T_0$
  ] else {
    $T_((#ind))$
  }
}

#let eventcensored(ind) = {
  if ind == [0] or ind == 0 [
      $macron(T)_0$
  ] else {
      $macron(T)_((#ind))$
  }
}

#let eventcensoredi(ind) = {
  if ind == [0] or ind == 0 [
      $macron(T)_(0,i)$
  ] else {
      $macron(T)_((#ind),i)$
  }
}

#let statuscensored(ind) = {
  if ind == [0] or ind == 0 [
      $macron(Delta)_0$
  ] else {
      $macron(Delta)_((#ind))$
  }
}

#let statuscensoredi(ind) = {
  if ind == [0] or ind == 0 [
      $macron(Delta)_(0,i)$
  ] else {
      $macron(Delta)_((#ind),i)$
  }
}

#let treatcensored(ind) = {
  if ind == [0] or ind == 0 [
      $A_0$
  ] else {
      $macron(A) (macron(T)_((#ind)))$
  }
}

#let treatcensoredi(ind) = {
  if ind == [0] or ind == 0 [
      $macron(A)_(0,i)$
  ] else {
      $macron(A)_((#ind),i)$
  }
}

#let covariatecensored(ind) = {
  if ind == [0] or ind == 0 [
      $L_0$
  ] else {
      $L (macron(T)_((#ind)))$
  }
}

#let covariatecensoredi(ind) = {
  if ind == [0] or ind == 0 [
      $L_(0,i)$
  ] else {
      $L_((#ind),i)$
  }
}

#let historycensored(ind) = {
  if ind == [0] or ind == 0 [
    $cal(F)_0$
  ] else [
      $cal(F)^tilde(beta)_(eventcensored(#ind))$
  ]
}

#let historycensoredi(ind) = {
  if ind == [0] or ind == 0 [
    $cal(F)_(0,i)$
  ] else [
      $cal(F)^tilde(beta)_((#ind),i)$
  ]
}

#let history(eventno) = {
  if eventno == [0] or eventno == 0 [
    $cal(F)_0$
  ] else [
    $cal(F)_(event(#eventno))$
  ]
}

#let cumhazardcensored(eventno, which, var) = {
    $tilde(Lambda)_(#eventno)^(#which)(#var, cal(F)^beta_(macron(T)_((#eventno - 1))))$
}
#let cumhazardcensoredprev(eventno, which, var) = {
    $tilde(Lambda)_(#eventno+1)^(#which)(#var, cal(F)^beta_(macron(T)_((#eventno))))$
}

#let historypast(eventno) = $underline(history(#eventno))$
#let historynext(eventno) = $overline(history(#eventno))$

#let hazard(which, var, eventno) = {
    $Lambda_(#eventno)^(#which)(#var, cal(F)_(T_((#eventno - 1))))$
}

#let cumhazard(eventno, which, var) = {
    $Lambda_(#eventno)^(#which)(#var, cal(F)_(T_((#eventno - 1))))$
}
#let cumhazardprev(eventno, which, var) = {
    $Lambda_(#eventno + 1)^(#which)(#var, cal(F)_(T_((#eventno))))$
}

#let treat(which) = {
    if which == [0] or which == 0 [
        $A(0)$
    ] else {
        $A(event(#which))$
    }
}

#let status(which) = {
    $Delta_((#which))$
}

#let statuscensored(which) = {
    $macron(Delta)_((#which))$
}

#let covariate(which) = {
    if which == [0] or which == 0 [
        $L(0)$
    ] else {
        $L(event(#which))$
    }
}

#let covariatecensored(which) = {
    if which == [0] or which == 0 [
        $L(0)$
    ] else {
        $L (macron(T)_(#which))$
    }
}

#let treatcensored(which) = {
    if which == [0] or which == 0 [
        $macron(A)_0$
    ] else {
        $A (macron(T)_(#which))$
    }
}

#let densitytrt(time, which) = $pi_(#which) (#time, covariate(#which), history(#which - 1))$
#let densitytrtnext(time, which) = $pi_(#which+1) (#time, covariate(#which + 1), treat(#which), H_(#which))$
#let densitytrtcensored(time, which) = $pi_(#which) (#time, covariatecensored(#which), historycensored(#which - 1))$
#let densitycova(time, arg, which) = $mu^a_(#which) (#time, #arg, history(#which - 1))$
#let densitycovl(time, arg, which) = $mu^ell_(#which) (#time, #arg, history(#which - 1))$
#let densitycovcensored(time, arg, which) = $mu_(#which) (#time, #arg, historycensored(#which - 1))$
#let evaluated(expr, size: 100%) = $lr(#expr|, size: #size)$
#let tauend = $tau_("end")$
#let unary(first, ..) = first
#let qquad = h(1.5cm)

#let Qbar(k) = $macron(Q)^g_(#k, tau)$
#let Qbarhat(k) = $hat(macron(Q))^g_(#k, tau)$
#let QbarL(k) = $macron(Q)^(g,-L)_(#k, tau)$
#let mean(k) = $bb(E)_#k$

#let prodint(s, t1, t2) = $product_(#s in (#t1, #t2])$
#let prodint2(s, t1, t2) = $product_(#s in (#t1, #t2))$

