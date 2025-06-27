# Model to use for the outcome regression which returns a prediction function
# for the chosen model.
# Available models are:
# \code{"tweedie"}, 
# \code{"quasibinomial"}, 
# \code{"scaled_quasibinomial"}, 
# \code{"ranger"}, 
# \code{"log_normal_mixture"}.
predict_iterative_conditional_expectation <- function(model_type,
                                                      history_of_variables,
                                                      data_ice) {
  if (model_type == "quasibinomial") {
    fit <- glm(
      as.formula(paste0(
        "weight ~ ", paste(history_of_variables, collapse = "+")
      )),
      data = data_ice,
      family = quasibinomial(link = "logit")
    )
    predict_fun <- function(data)
      predict(fit, data, type = "response")
  } else if (model_type == "tweedie") {
    fit <- glm(
      as.formula(paste0(
        "weight ~ ", paste(history_of_variables, collapse = "+")
      )),
      data = data_ice,
      family = statmod::tweedie(var.power = 1.5)
    )
    predict_fun <- function(data)
      predict(fit, data, type = "response")
  } else if (model_type == "scaled_quasibinomial") {
    max_weight <- max(data_ice$weight)
    data_ice$f_weight <- data_ice$weight / max_weight
    fit <- glm(as.formula(paste0(
      "f_weight ~ ", paste(history_of_variables, collapse = "+")
    )), data = data_ice, family = quasibinomial)
    predict_fun <- function(data)
      predict(fit, data, type = "response") * max_weight
  } else if (model_type == "ranger") {
    fit <- ranger::ranger(as.formula(paste0(
      "weight ~ ", paste(history_of_variables, collapse = "+")
    )), data = data_ice)
    predict_fun <- function(data)
      predict(fit, data = data)$predictions
  } else if (model_type == "log_normal_mixture") {
    fit_prob <- glm(as.formula(paste0(
      "weight > 1 ~ ", paste(history_of_variables, collapse = "+")
    )), data = data_ice, family = binomial)
    data_ice$weightminusone <- data_ice$weight - 1
    fit_normal <- lm(as.formula(paste0(
      "log(weight) ~ ",
      paste(history_of_variables, collapse = "+")
    )), data = data_ice[get("weight") > 1])
    predict_fun <- function(data)
      predict(fit_prob, data, type = "response") * (exp(predict(fit_normal, data, type = "response")))
  } else {
    stop("Unknown model type. Please choose from: 'tweedie', 'quasibinomial', 'scaled_quasibinomial', 'ranger', 'log_normal_mixture'.")
  }
  predict_fun
}

# coph learner for censoring
learn_coxph <- function(character_formula,
                        data,
                        intervened_data = NULL,
                        type = "survival") {
  ## Fit the Cox model
  fit <- coxph(character_formula, data = data, x = TRUE)
  if (!is.null(intervened_data)) {
    ## Predict on intervened data
    list(pred=predict(fit, newdata = intervened_data, type = type), fit = fit)
  } else {
    ## Predict on original data
    list(pred=predict(fit, type = type), fit = fit)
  }
}

learn_glm_logistic <- function(character_formula,
                               data) {
  ## Fit the logistic regression model
  fit <- glm(character_formula, data = data, family = binomial(link = "logit"))
  ## Predict on original data
  list(pred=predict(fit, type = "response"), fit = fit)
}
