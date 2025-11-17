-- Define functions to lock and unlock artifacts/
lockArtifacts = () -> (
    run("chmod -R u-w " | projectDirectory | "artifacts");
)

unlockArtifacts = () -> (
    run("chmod -R u+w " | projectDirectory | "artifacts");
)
