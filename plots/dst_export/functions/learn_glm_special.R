### learn_glm_special.R ---
#----------------------------------------------------------------------
## author:
## created: aug 19 2025 (16:24)
## Version:
## last-updated: sep  2 2025 (15:00) 
##     Update #: 41
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

learn_glm_logistic_special <- function(character_formula,
                                       data) {
  fr <- as.formula(character_formula)
  a_rhs <- labels(terms(fr))[grepl("A_", labels(terms(fr)))]
  if (length(a_rhs) > 0) {
    rhs <- labels(terms(fr))[!grepl("A_", labels(terms(fr)))]
    out <- as.character(fr[[2]])
    formula_object <- as.formula(paste0(out, "~", paste0(rhs, collapse = "+")))
    ## Fit the logistic regression model
    fit <- glm(formula_object, data = data[rowSums(data[, ..a_rhs]) > 0], family = binomial(link = "logit"))
    pred_fun <- function(x, newdata) {
      pred <- rep(0, nrow(newdata))
      part <- rowSums(newdata[, ..a_rhs]) > 0
      pred[part] <- predict(x, newdata = newdata[part], type = "response")
      pred
    }
    ##browser(skipCalls=1L)
    pred <- pred_fun(fit, data)
  } else {
    fit <- glm(fr, data = data, family = binomial(link = "logit"))
    pred <- predict(fit, newdata = data, type = "response")
  }
  if (any(is.na(pred))) {
    stop("predictions contain NAs")
  }
  if (any(pred > 1)) {
    warning("predictions above 1")
    pred <- pmin(pred, 1)
  }
  if (any(pred < 0)) {
    warning("predictions below 0")
    pred <- pmax(pred, 0)
  }
  ## Predict on original data
  list(pred = pred, predict_fun = fit)
}

#----------------------------------------------------------------------
### learn_glm_special.R ends here
