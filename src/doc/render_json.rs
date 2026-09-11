//! Machine-readable JSON dump of the doc model.

use std::path::Path;

use super::model::DocModel;

pub fn write(model: &DocModel, path: &Path) -> Result<(), String> {
    let text = serde_json::to_string_pretty(model).map_err(|e| e.to_string())?;
    std::fs::write(path, text).map_err(|e| format!("writing {}: {e}", path.display()))
}
