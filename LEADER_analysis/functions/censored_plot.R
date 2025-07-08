censored_plot <- function(df, reg = "lira", tau, outcomes = c("all_cause_mortality", "mace", "censored")) {
  fit <- survfit(Surv(time, X == "censored") ~ 1, data = df)
  p <- ggsurvplot(fit, data = df, xlim = c(0, tau))

  df <- df[X %in% outcomes | (X == reg & reg_val == 0), env = list(reg_val = reg)]
  ## keep the earlies time for each id
  setkey(df, id, time)
  df <- df[, .SD[1], by = id]
  df$stat <- 1
  fit <- survfit(Surv(time, stat) ~ 1, data = df)
  r <- ggsurvplot(fit, data = df, xlim = c(0, tau))
  list(
    plot_censored = p,
    plot_dropout = r
  )
}
