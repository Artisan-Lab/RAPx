use std::fs::{remove_file, File};
use std::io::Write;
use std::process::Command;

// please ensure 'graphviz' has been installed
pub fn render_dot_graphs(dot_graphs: Vec<String>) {
    Command::new("mkdir")
        .args(["UPG"])
        .output()
        .expect("Failed to create directory");

    for (index, dot) in dot_graphs.into_iter().enumerate() {
        let file_name = format!("graph{}.dot", index);
        let mut file = File::create(&file_name).expect("Unable to create file");
        file.write_all(dot.as_bytes())
            .expect("Unable to write data");

        Command::new("dot")
            .args([
                "-Tpng",
                &file_name,
                "-o",
                &format!("UPG/graph{}.png", index),
            ])
            .output()
            .expect("Failed to execute Graphviz dot command");

        remove_file(&file_name).expect("Failed to delete .dot file");
    }
}
