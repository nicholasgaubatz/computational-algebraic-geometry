-- A script to run at the beginning of every session. Loads all files in src/ and defines functions to lock and unlock artifacts.

-- Set the home directory. Change this depending on where you are on your machine.
projectDirectory = ""

-- Store the /src/ directory for easy access.
srcDirectory = projectDirectory | "src/"

-- Add files to load here. TODO: figure out whether this can be automated to load all files in the directory.
load(srcDirectory | "aot.m2")
load(srcDirectory | "artifacts_locking.m2")
load(srcDirectory | "generator.m2")
load(srcDirectory | "graphic.m2")
load(srcDirectory | "misc.m2")
load(srcDirectory | "wlp.m2")


