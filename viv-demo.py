#!/usr/bin/env python3
"""
Viv Demo Tool

Use this tool to try the viv tool on pre-packaged bugs.
It downloads artifacts, switches to the appropriate Git branch, and runs viv.
"""

import os
import sys
import subprocess
import tempfile
import urllib.request
import shutil
import textwrap
from dataclasses import dataclass

SHELL_WHITE_BOLD = "\033[1;37m"
SHELL_END = "\033[0m"


@dataclass
class Bug:
    name: str
    description: str
    git_revision: str
    artifact_url: str


# Pre-packaged bugs with their corresponding data
BUGS = [
    Bug(
        name="dside_accesses_shift",
        description="Error in pending data accesses shifting.",
        git_revision="bug/dside-accesses-shift",
        artifact_url="https://silogy-demo-bug-artifacts.s3.us-east-1.amazonaws.com/dside-accesses-shift.tar.gz"
    ),
    Bug(
        name="handle_misaligned",
        description="An erroneous grant signal in the cache causes byte enables for cache lines to be incorrect, "
                    "causing some data to be unwritten to memory.",
        git_revision="bug/handle-misaligned",
        artifact_url="https://silogy-demo-bug-artifacts.s3.us-east-1.amazonaws.com/handle-misaligned.tar.gz"
    ),
    Bug(
        name="opcode_decode",
        description="The decoder's opcode logic is shifted by a bit, causing erroneous instructions to appear.",
        git_revision="bug/opcode-decode",
        artifact_url="https://silogy-demo-bug-artifacts.s3.us-east-1.amazonaws.com/opcode-decode.tar.gz"
    ),
]


def display_bugs() -> None:
    """Display available bugs for selection."""
    print("Available bugs for demonstration:")
    for i, bug in enumerate(BUGS, 1):
        print(f"{i}. {SHELL_WHITE_BOLD}{bug.name}{SHELL_END} (branch: {bug.git_revision})")
        wrapped_description = textwrap.fill(bug.description, width=90, initial_indent="   ", subsequent_indent="   ")
        print(wrapped_description)
        print()


def get_user_selection() -> Bug:
    """Get user's bug selection."""
    while True:
        try:
            choice = input(f"Please select a bug for Viv to debug. (1-{len(BUGS)}) ").strip()
            if not choice:
                continue

            index = int(choice) - 1
            if 0 <= index < len(BUGS):
                return BUGS[index]
            else:
                print(f"Please enter a number between 1 and {len(BUGS)}")
        except ValueError:
            print("Please enter a valid number")
        except KeyboardInterrupt:
            print("\nExiting...")
            sys.exit(0)


def download_artifact(url: str, dest_path: str) -> None:
    """Download artifact from URL to destination path."""
    print(f"Downloading artifact from {url}...")
    try:
        urllib.request.urlretrieve(url, dest_path)
        print(f"Downloaded to {dest_path}")
    except Exception as e:
        print(f"Error downloading artifact: {e}")
        sys.exit(1)


def get_git_diff(revision: str) -> str:
    """Get git diff for the specified revision."""
    try:
        # Fetch all remote branches first
        subprocess.run(["git", "fetch", "origin"], capture_output=True, check=True)

        # Get the diff from the revision's HEAD
        result = subprocess.run(
            ["git", "show", "--no-merges", f"origin/{revision}"],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"Error getting git diff: {e}")
        return f"Could not retrieve diff for {revision}"


def confirm_execution(bug: Bug, artifact_path: str) -> bool:
    """Display diff and command, then ask for confirmation."""
    print(f"\n{SHELL_WHITE_BOLD}=== Git Diff for {bug.git_revision} ==={SHELL_END}")
    diff = get_git_diff(bug.git_revision)
    print(diff)

    print(f"\n{SHELL_WHITE_BOLD}=== Command to be executed ==={SHELL_END}")
    viv_command = f"viv submit --job-name={bug.name} --artifact-path={artifact_path}"
    print(viv_command)

    print(f"\n{SHELL_WHITE_BOLD}Continue with execution? (Y/n):{SHELL_END} ", end="")

    try:
        response = input().strip().lower()
        return response in ("", "y", "yes")
    except KeyboardInterrupt:
        return False


def switch_git_branch(revision: str) -> None:
    """Switch to the specified git revision."""
    print(f"Switching to git revision: {revision}")
    try:
        # Check if we're in a git repository
        subprocess.run(
            ["git", "rev-parse", "--is-inside-work-tree"],
            capture_output=True,
            text=True,
            check=True
        )

        # Fetch latest changes
        subprocess.run(["git", "fetch", "origin"], check=True)

        # Switch to the revision
        subprocess.run(["git", "checkout", f"origin/{revision}"], check=True)
        print(f"Successfully switched to {revision}")

    except subprocess.CalledProcessError as e:
        print(f"Error switching git branch: {e}")
        print("Make sure you're in a git repository and the revision exists")
        sys.exit(1)


def run_viv(job_name: str, artifact_path: str) -> None:
    """Run the viv tool with the specified parameters."""
    print(f"Running viv submit --artifact-path={artifact_path}")
    try:
        subprocess.run([
            "viv", "submit",
            f"--job-name={job_name}",
            f"--artifact-path={artifact_path}"
        ], check=True)

        print("Viv execution completed successfully!")

    except subprocess.CalledProcessError as e:
        print(f"Error running viv: {e}")
        sys.exit(1)
    except FileNotFoundError:
        print("Error: 'viv' command not found. Make sure viv is installed and in your PATH.")
        sys.exit(1)


def cleanup_temp_files(temp_dir: str) -> None:
    """Clean up temporary files."""
    try:
        shutil.rmtree(temp_dir)
        print(f"Cleaned up temporary files in {temp_dir}")
    except Exception as e:
        print(f"Warning: Could not clean up temporary files: {e}")


def main() -> None:
    """Main function."""
    print(f"{SHELL_WHITE_BOLD}Viv Demo Tool{SHELL_END}")
    print()

    display_bugs()

    # Get user selection
    selected_bug = get_user_selection()
    print(f"Selected: {selected_bug.name}")
    print()

    temp_dir = tempfile.mkdtemp(prefix="viv_demo_")
    artifact_path = os.path.join(temp_dir, "artifacts.tar.gz")

    try:
        # Show diff and get confirmation before proceeding
        if not confirm_execution(selected_bug, artifact_path):
            print("Operation cancelled by user")
            return

        download_artifact(selected_bug.artifact_url, artifact_path)
        switch_git_branch(selected_bug.git_revision)
        run_viv(selected_bug.name, artifact_path)
    except KeyboardInterrupt:
        print("\nOperation cancelled by user")
        sys.exit(0)
    finally:
        cleanup_temp_files(temp_dir)


if __name__ == "__main__":
    main()
