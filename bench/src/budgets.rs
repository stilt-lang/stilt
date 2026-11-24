//! The budgets of `budgets.toml`: a number for each key of each goal's table (Goals, Enforcement).

use std::collections::HashMap;

/// The budgets, by goal and key.
#[derive(Debug, Default)]
pub(crate) struct Budgets(HashMap<(String, String), f64>);

impl Budgets {
    /// Reads the budgets from the text of `budgets.toml`: tables named after goals, each holding
    /// `key = number` lines, and comments after `#`.
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        let mut table: Option<String> = None;
        let mut budgets = HashMap::new();
        for (n, line) in text.lines().enumerate() {
            let line = line.split('#').next().unwrap_or_default().trim();
            if line.is_empty() {
                continue;
            }
            if let Some(name) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
                table = Some(name.trim().to_owned());
                continue;
            }
            let at = |what: &str| format!("budgets.toml, line {}: {what}", n + 1);
            let (key, value) = line
                .split_once('=')
                .ok_or_else(|| at("expected `key = number`"))?;
            let table = table
                .clone()
                .ok_or_else(|| at("a budget outside a table"))?;
            let value = value.trim();
            let number = value
                .parse()
                .map_err(|_| at(&format!("`{value}` isn't a number")))?;
            budgets.insert((table, key.trim().to_owned()), number);
        }
        Ok(Self(budgets))
    }

    /// The budget `key` of `goal`.
    pub(crate) fn get(&self, goal: &str, key: &str) -> Result<f64, String> {
        self.0
            .get(&(goal.to_owned(), key.to_owned()))
            .copied()
            .ok_or_else(|| format!("budgets.toml has no `{key}` for {goal}"))
    }
}

#[cfg(test)]
mod tests {
    use super::Budgets;

    #[test]
    fn each_budget_is_found_by_its_goal_and_key() {
        let text = "# budgets\n[debug-speed]\ngeomean = 5.0 # the mean\n\n[free-success]\nmicrobenchmark = 1.1\n";
        let budgets = Budgets::parse(text).expect("the budgets parse");
        assert_eq!(budgets.get("debug-speed", "geomean"), Ok(5.0));
        assert_eq!(budgets.get("free-success", "microbenchmark"), Ok(1.1));
        assert!(budgets.get("free-success", "geomean").is_err());
    }

    #[test]
    fn a_line_that_isnt_a_budget_is_refused_with_its_number() {
        let error =
            Budgets::parse("[debug-speed]\ngeomean = five\n").expect_err("five isn't a number");
        assert_eq!(error, "budgets.toml, line 2: `five` isn't a number");
        let error = Budgets::parse("geomean = 5\n").expect_err("a budget needs a table");
        assert_eq!(error, "budgets.toml, line 1: a budget outside a table");
    }
}
