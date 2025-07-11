# Model to use for the outcome regression which returns a prediction function
# for the chosen model.
# Available models are:
# \code{"tweedie"},
# \code{"quasibinomial"},
# \code{"scaled_quasibinomial"},
# \code{"ranger"},
# \code{"log_normal_mixture"}.
# \code{"lm"}.
learn_Q <- function(model_type,
                    history_of_variables,
                    data_ice,
                    outcome_name = "weight") {
  max_weight <- max(data_ice$weight)
  if (is.null(max_weight) || is.na(max_weight)) {
    stop("The 'weight' column in data_ice must not be NULL or NA.")
  }
  if (max_weight == 0) {
    predict_fun <- function(data) {
      warning("All weights are zero. Returning a constant prediction of zero.")
      rep(0, nrow(data))
    }
  } else {
    if (model_type == "quasibinomial") {
      fit <- glm(
        as.formula(paste0(
          outcome_name,
          " ~ ", paste(history_of_variables, collapse = "+")
        )),
        data = data_ice,
        family = quasibinomial(link = "logit")
      )
      predict_fun <- function(data) {
        predict(fit, data, type = "response")
      }
    } else if (model_type == "tweedie") {
      fit <- glm(
        as.formula(paste0(
          outcome_name,
          " ~ ", paste(history_of_variables, collapse = "+")
        )),
        data = data_ice,
        family = statmod::tweedie(var.power = 1.5)
      )
      predict_fun <- function(data) {
        predict(fit, data, type = "response")
      }
    } else if (model_type == "scaled_quasibinomial") {
      data_ice$f_weight <- data_ice[[outcome_name]] / max_weight
      fit <- glm(
        as.formula(paste0(
          "f_weight ~ ", paste(history_of_variables, collapse = "+")
        )),
        data = data_ice,
        family = quasibinomial
      )
      predict_fun <- function(data) {
        predict(fit, data, type = "response") * max_weight
      }
    } else if (model_type == "ranger") {
      fit <- ranger::ranger(as.formula(paste0(
        outcome_name,
        " ~ ", paste(history_of_variables, collapse = "+")
      )), data = data_ice)
      predict_fun <- function(data) {
        predict(fit, data = data)$predictions
      }
    } else if (model_type == "log_normal_mixture") {
      fit_prob <- glm(
        as.formula(paste0(
          outcome_name,
          " > 1 ~ ", paste(history_of_variables, collapse = "+")
        )),
        data = data_ice,
        family = binomial
      )
      data_ice$weightminusone <- data_ice$weight - 1
      fit_normal <- lm(as.formula(paste0(
        "log(", outcome_name, ") ~ ",
        paste(history_of_variables, collapse = "+")
      )), data = data_ice[get("weight") > 1])
      predict_fun <- function(data) {
        predict(fit_prob, data, type = "response") * (exp(predict(fit_normal, data, type = "response")))
      }
    } else if (model_type == "lm") {
      fit <- lm(as.formula(paste0(
        outcome_name,
        " ~ ", paste(history_of_variables, collapse = "+")
      )), data = data_ice)
      predict_fun <- function(data) {
        pred <- predict(fit, data, type = "response")
        ## Ensure predictions are non-negative
        pred[pred < 0] <- 0
        return(pred)
      }
    } else {
      formula_w <- paste0(
        outcome_name,
        " ~ ", paste(history_of_variables, collapse = "+")
      )
      predict_fun <- do.call(model_type, list(
        character_formula = formula_w,
        data = data_ice
      ))$predict_fun
    }
  }
  predict_fun
}

## Example function
learn_h2o <- function(character_formula,
                      data,
                      intervened_data = NULL,
                      max_runtime_secs = 30,
                      nfolds = 10,
                      verbose = FALSE,
                      ...) {
  requireNamespace("h2o", quietly = TRUE)
  formula_object <- as.formula(character_formula)
  outcome_name <- as.character(formula_object[[2]])
  history_of_variables <- labels(terms(formula_object))
  data <- data[, c(outcome_name, history_of_variables), with = FALSE]
  ## Check if only 0/1 values in outcome_name
  if (all(data[[outcome_name]] %in% c(0, 1))) {
    distribution <- "bernoulli"
    data[[outcome_name]] <- as.factor(data[[outcome_name]]) # Convert to factor for classification
  } else {
    distribution <- "AUTO"
  }

  if (!verbose) sink("/dev/null") # Suppress H2O output
  suppressWarnings({
    h2o::h2o.init()
  })
  data_h2o <- as.h2o(data)

  ## AutoML
  aml <- h2o.automl(
    y = outcome_name,
    training_frame = data_h2o,
    max_runtime_secs = max_runtime_secs,
    nfolds = nfolds,
    distribution = distribution,
    sort_metric = "MSE",
    ...
  )
  if (!verbose) sink()

  best_model <- aml@leader
  leaderboard <- as.data.table(aml@leaderboard)

  ## Print leader and glm
  leader <- aml@leaderboard[1, ]
  lm_models <- leaderboard[grepl("LM", leaderboard$model_id), ]
  leaderboard <- rbind(leader, lm_models)
  print(leaderboard)

  if (distribution == "bernoulli") {
    ## For binary, we need to convert the predictions to a vector
    predict_fun <- function(data) {
      newdata_h2o <- as.h2o(data)
      as.vector(h2o.predict(best_model, newdata = newdata_h2o)$p1) # p1 for class 1 probability
    }
  } else {
    ## For regression, we can directly use the predict method
    predict_fun <- function(data) {
      newdata_h2o <- as.h2o(data)
      as.vector(h2o.predict(best_model, newdata = newdata_h2o)$predict)
    }
  }
  if (is.null(intervened_data)) {
    return(list(pred = predict_fun(data), predict_fun = predict_fun))
  } else {
    return(predict_fun(intervened_data))
  }
}

# coph learner for censoring
learn_coxph <- function(character_formula,
                        data) {
  formula_cox <- as.formula(character_formula)
  ## Fit the Cox model
  fit <- coxph(formula_cox, data = data, x = TRUE)
  baseline_hazard_minus <- as.data.table(basehaz(fit, centered = FALSE))
  baseline_hazard_minus$hazard <- c(0, head(baseline_hazard_minus$hazard, -1))
  setnames(baseline_hazard_minus, "time", as.character(formula_cox[[2]][2]))
  baseline_hazard_minus <- baseline_hazard_minus[data, roll = TRUE, on = as.character(formula_cox[[2]][2])]
  baseline_hazard_minus[, exp_lp := predict(fit, newdata = .SD, type = "risk", reference = "zero")]
  baseline_hazard_minus[, surv := exp(-exp_lp * hazard)]
  list(pred = baseline_hazard_minus$surv, fit = fit)
}

learn_glm_logistic <- function(character_formula,
                               data) {
  formula_object <- as.formula(character_formula)
  ## Fit the logistic regression model
  fit <- glm(formula_object, data = data, family = binomial(link = "logit"))
  ## Predict on original data
  list(pred = predict(fit, type = "response"), predict_fun = fit)
}
