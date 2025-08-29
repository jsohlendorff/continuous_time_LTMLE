math_names <- data.frame(
  name = c("effect_A_on_Y", "effect_L_on_Y", "effect_L_on_A", "effect_A_on_L", 
           "effect_age_on_Y", "effect_age_on_A", "baseline_rate_Y", "baseline_rate_C", "a_intercept", "n"),
  math_name = c("beta[A]^y", 
                "beta[L]^y",
                "alpha[L]",
                "beta[A]^\U2113",
                "beta[age]^y",
                "alpha[age]",
                "lambda[y]",
                "lambda[c]",
                "alpha[0]",
                "n")
)

## Function to create a boxplot of the estimates and standard errors
fun_boxplot <- function(d, by = NULL, sample_size = FALSE, single_type_se=FALSE,
                        ln_width = 1,
                        cbbPalette = c("#000000", "#E69F00", "#56B4E9", "#009E73", "#D55E00", "#0072B2", "#CC79A7", "#F0E442")) {
  d$type <- factor(d$type)
  levels(d$type)[levels(d$type) == "Debiased ICE-IPCW"] <- "ICE-IPCW (Debiased)"
  levels(d$type)[levels(d$type) == "LTMLE (grid size = 8)"] <- "LTMLE"
  if (sample_size){
    scales <- "free_y"
  } else {
    scales <- "fixed"
  }
  if (!is.null(by)) {
    ## delete values of by that do not have more than one value in d
    by <- by[sapply(by, function(x)
      length(unique(d[[x]])) > 1)]
  }
  ipw_ice_results <- na.omit(
    melt(
      d,
      id.vars = c(by, "value"),
      measure.vars =  "ice_ipcw_estimate", #c("ipw", "ice_ipcw_estimate"),
      variable.name = "type",
      value.name = "estimate"
    )
  )
  ipw_ice_results[, c("se", "lower", "upper") := NA]
  ## rename levels of type from ipw, ice_ipcw_estimate to Inverse Probability Weighting, ICE-IPCW
  ipw_ice_results$type <- factor(
    ipw_ice_results$type,
    levels =  "ice_ipcw_estimate", #c("ipw", "ice_ipcw_estimate"),
    labels = "ICE-IPCW" #c("Inverse Probability Weighting", )
  )
  cols_to_remove <- grepl("method|tar|ice_ipcw_estimate|ipw", names(d))
  d <- d[, !cols_to_remove, with = FALSE]
  d <- rbind(d, ipw_ice_results, fill = TRUE)
  
  d[, sd_est := sd(estimate), by = c(by, "type")]
  ## For all names in `by`, reformat them to `latex names` =  level
  ## e.g, \\beta=0
  for (b in by) {
    math_name <- math_names$math_name[match(b, math_names$name)]
    d[, (b) := as.factor(get(b))]
    levels(d[[b]]) <- paste0(math_name, "==", levels(d[[b]]))
  }

  p <- ggplot2::ggplot(data = d, aes(y = estimate, color = type)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(aes(yintercept = value), linewidth = ln_width) +
    ggplot2::theme_minimal(base_size = 13) +
    ylab("Estimates") +
    scale_color_manual(name = "Estimator", values = cbbPalette) +
    theme(
      axis.title.x = element_blank(),
      axis.text.x = element_blank(),
      axis.ticks.x = element_blank(),
    ) 
  d_se <- copy(d)
  d_se <- d_se[!type %in% c("ICE-IPCW", "Inverse Probability Weighting", "Naive Cox")]
  if (!single_type_se) {
    qz <- ggplot2::ggplot(data = d_se, aes(y = se, color = type)) + scale_color_manual(name = "Estimator", values = cbbPalette)
  } else {
    qz <- ggplot2::ggplot(data = d_se, aes(y = se)) 
  }
  qz <- qz +
    ggplot2::geom_boxplot() +
    ggplot2::theme_minimal(base_size = 13) +
    ylab("Standard Errors") +
    theme(
      axis.title.x = element_blank(),
      axis.text.x = element_blank(),
      axis.ticks.x = element_blank()
    )
  p <- p + ggplot2::facet_wrap(as.formula(paste("~", paste(by, collapse = "+"))),
                               labeller = ggplot2::label_parsed,
                               nrow = 1) + scale_y_continuous(labels = scales::percent)
  
  qz <- qz + ggplot2::facet_wrap(as.formula(paste("~", paste(by, collapse = "+"))),
                                 labeller = ggplot2::label_parsed,
                                 nrow = 1,
                                 scales = scales) + 
    ggplot2::geom_hline(aes(yintercept = sd_est), linetype = "dashed")
  if (!single_type_se) {
    qz <- qz + ggplot2::geom_hline(aes(yintercept = sd_est, color = type), linetype = "dashed", linewidth = ln_width)
  } else {
    qz <- qz + ggplot2::geom_hline(aes(yintercept = sd_est), linetype = "dashed", linewidth = ln_width)
  }
  list(p, qz)
}

## Function to create a boxplot of the estimates and standard errors
fun_boxplot_censoring <- function(d, by = NULL,
                                  ln_width = 0.8,
                                  cbbPalette = c("#000000", "#E69F00", "#56B4E9", "#009E73", "#D55E00", "#0072B2", "#CC79A7", "#F0E442")) {
  if (!is.null(by)) {
    ## delete values of by that do not have more than one value in d
    by <- by[sapply(by, function(x) length(unique(d[[x]])) > 1)]
  }
  d$model_type <- factor(
    d$model_type,
    levels = c("scaled_quasibinomial", "tweedie", "lm"),
    labels = c("Scaled Quasi-binomial", "Tweedie", "Linear model")
  )
  d[, baseline_rate_C := factor(baseline_rate_C)]
  d[, model_type := factor(model_type)]
  d[, sd_est := sd(estimate), by = c(by, "model_type", "baseline_rate_C")]
  for (b in c(by, "baseline_rate_C")) {
    math_name <- math_names$math_name[match(b, math_names$name)]
    d[, (b) := paste0(math_name, "==", get(b))]
  }
  p <- ggplot2::ggplot(data = d, aes(y = estimate, color = model_type)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(aes(yintercept = value), linewidth = ln_width) +
    ggplot2::theme_minimal(base_size = 13) + 
    ylab("Estimates") + 
    scale_color_manual(name = "Model type (ICE)", values = cbbPalette) +
    theme(
      axis.title.x = element_blank(),
      axis.text.x = element_blank(),
      axis.ticks.x = element_blank()
    )
  qz <- ggplot2::ggplot(data = d, aes(y = se, color = model_type)) +
    ggplot2::geom_boxplot() +
    ggplot2::theme_minimal(base_size = 13) + 
    ylab("Standard Errors") + 
    scale_color_manual(name = "Model type (ICE)", values = cbbPalette) +
    theme(
      axis.title.x = element_blank(),
      axis.text.x = element_blank(),
      axis.ticks.x = element_blank()
    )
  r <- ggplot2::ggplot(data = d, aes(y = ice_ipcw_estimate, color = model_type)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(aes(yintercept = value), linewidth = ln_width) +
    ggplot2::theme_minimal(base_size = 13) + 
    ylab("ICE-IPCW Estimates") + 
    scale_color_manual(name = "Model type (ICE)", values = cbbPalette) +
    theme(
      axis.title.x = element_blank(),
      axis.text.x = element_blank(),
      axis.ticks.x = element_blank()
    )
  if (!is.null(by)) {
    p <- p + ggplot2::facet_grid(as.formula(paste("baseline_rate_C~", paste(by, collapse = "+"))), labeller = ggplot2::label_parsed)
    qz <- qz + ggplot2::facet_grid(as.formula(paste("baseline_rate_C~", paste(by, collapse = "+"))), labeller = ggplot2::label_parsed)
    ## for q add different geom hlines with sd(estimate) for each compination of variables in by
    qz <- qz + ggplot2::geom_hline(aes(yintercept = sd_est, color = model_type), linetype = "dashed", linewidth = ln_width)
    r <- r + ggplot2::facet_grid(as.formula(paste("baseline_rate_C~", paste(by, collapse = "+"))), labeller = ggplot2::label_parsed)
  } else {
    qz <- qz + ggplot2::geom_hline(aes(yintercept = sd(estimate), color = "red", linewidth = ln_width))
  }
  p <- p + scale_y_continuous(labels = scales::percent)
  r <- r + scale_y_continuous(labels = scales::percent)
  list(p, qz, r)
}

fun_boxplot_censoring_non_conservative <- function(d, by = NULL) {
  if (!is.null(by)) {
    ## delete values of by that do not have more than one value in d
    by <- by[sapply(by, function(x) length(unique(d[[x]])) > 1)]
  }
  d[, baseline_rate_C := factor(baseline_rate_C)]
  ## concatenate cens_mg_method and grid_size
  d[, cens_mg_method_grid_size := paste(cens_mg_method, grid_size, sep = "_")]
  d[, sd_est := sd(estimate), by = c(by, "model_type", "baseline_rate_C", "cens_mg_method_grid_size")]
  for (b in c(by, "baseline_rate_C")) {
    math_name <- math_names$math_name[match(b, math_names$name)]
    d[, (b) := paste0(math_name, "==", get(b))]
  }
  ## interaction for
  ## d[, gr := do.call(paste, c(.SD, sep = "_")), .SDcols = by]
  p <- ggplot2::ggplot(data = d, aes(y = estimate, color = cens_mg_method_grid_size)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(aes(yintercept = value)) +
    ggplot2::theme_minimal()
  ## in d add interaction between model_type and baseline_rate_C
  qz <- ggplot2::ggplot(data = d, aes(y = se, color = cens_mg_method_grid_size)) +
    ggplot2::geom_boxplot() +
    ggplot2::theme_minimal()
  r <- ggplot2::ggplot(data = d, aes(y = ice_ipcw_estimate, color = cens_mg_method_grid_size)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(aes(yintercept = value, color = model_type)) +
    ggplot2::theme_minimal()
  ## w <- ggplot2::ggplot(data = d, aes(y = ipw)) +
  ##   ggplot2::geom_boxplot() +
  ##   ggplot2::geom_hline(aes(yintercept = value, color = "red")) +
  ##   ggplot2::theme_minimal()
  if (!is.null(by)) {
    p <- p + ggplot2::facet_grid(as.formula(paste("baseline_rate_C~", paste(by, collapse = "+"))), scales = "free_y", labeller = ggplot2::label_parsed)
    qz <- qz + ggplot2::facet_grid(as.formula(paste("baseline_rate_C~", paste(by, collapse = "+"))), scales = "free_y", labeller = ggplot2::label_parsed)
    ## for q add different geom hlines with sd(estimate) for each compination of variables in by
    qz <- qz + ggplot2::geom_hline(aes(yintercept = sd_est, color = cens_mg_method_grid_size), linetype = "dashed")
    r <- r + ggplot2::facet_grid(as.formula(paste("baseline_rate_C~", paste(by, collapse = "+"))), scales = "free_y", labeller = ggplot2::label_parsed)
    #w <- w + ggplot2::facet_grid(as.formula(paste("baseline_rate_C~", paste(by, collapse = "+"))), scales = "free_y", labeller = ggplot2::label_parsed)
  } else {
    qz <- qz + ggplot2::geom_hline(aes(yintercept = sd(estimate), color = "red"))
  }
  p <- p + scale_y_continuous(labels = scales::percent)
  r <- r + scale_y_continuous(labels = scales::percent)
  list(p, qz, r)
}

## Calculate info for tables, i.e., coverage, mean squared error, bias, standard errors
get_tables <- function(results, by = NULL, remove_duplicate_parameters = TRUE) {
  results$type <- factor(results$type)
  levels(results$type)[levels(results$type) == "Debiased ICE-IPCW"] <- "ICE-IPCW (Debiased)"
  levels(results$type)[levels(results$type) == "LTMLE (grid size = 8)"] <- "LTMLE"
  if (!is.null(by)) {
    ## delete values of by that do not have more than one value in d
    by <- by[sapply(by, function(x) length(unique(results[[x]])) > 1)]
  }
  ## remove all methods columns
  ipw_ice_results <- na.omit(
    melt(
      results,
      id.vars = c(by, "value"),
      measure.vars = "ice_ipcw_estimate", #c("ipw", "ice_ipcw_estimate"),
      variable.name = "type",
      value.name = "estimate"
    )
  )
  ipw_ice_results[, c("se", "lower", "upper") := NA]
  ## rename levels of type from ipw, ice_ipcw_estimate to Inverse Probability Weighting, ICE-IPCW
  ipw_ice_results$type <- factor(ipw_ice_results$type,
                                 levels = c("ipw", "ice_ipcw_estimate"),
                                 labels = c("Inverse Probability Weighting", "ICE-IPCW")
  )
  cols_to_remove <- grepl("method|tar|ice_ipcw_estimate|ipw", names(results))
  results <- results[, !cols_to_remove, with = FALSE]
  results <- rbind(results, ipw_ice_results, fill = TRUE)
  results <- results[, .(
    coverage = mean((value > lower) & (value < upper)),
    mse = mean((estimate - value)^2),
    bias = mean(estimate - value),
    sd = sd(estimate),
    mean_se = mean(se)
  ),
  by = c(by, "type")]
  results <- as.data.table(results)
  setkeyv(results, c(by, "type"))
  if (remove_duplicate_parameters) {
    by <- setdiff(by, "model_type")
    for (b in by) {
      if ("model_type" %in% names(results)) {
        results[type != "ICE-IPCW (Debiased)" | model_type != "scaled_quasibinomial", (b) := NA]
      } else {
        results[type != "ICE-IPCW (Debiased)", (b) := NA]
      }
    }
  }
  results
}

## Simple function for calculating true value in simulation studies
## NOTE: We allow for administrative censoring in this calculation
calculate_mean <- function(data_interventional, tau) {
  data_interventional$timevarying_data[event %in% c("tauend", "Y", "D"), mean(event == "Y" & time <= tau)]
}
