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
from dataclasses import dataclass


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
        description="Error in pending data accesses shifting",
        git_revision="bug/dside-accesses-shift",
        artifact_url="https://silogy-demo-bug-artifacts.s3.us-east-1.amazonaws.com/dside-accesses-shift.tar.gz"
    ),
    Bug(
        name="handle_misaligned",
        description=" An erroneous grant signal in the cache causes byte enables for cache lines to be incorrect, causing some data to be unwritten to memory",
        git_revision="bug/handle-misaligned",
        artifact_url="https://silogy-demo-bug-artifacts.s3.us-east-1.amazonaws.com/handle-misaligned.tar.gz"
    ),
    Bug(
        name="opcode_decode",
        description="The decoder's opcode logic is shifted by a bit, causing erroneous instructions to appear",
        git_revision="bug/opcode-decode",
        artifact_url="https://silogy-demo-bug-artifacts.s3.us-east-1.amazonaws.com/opcode-decode.tar.gz"
    ),
]


def display_bugs() -> None:
    """Display available bugs for selection."""
    print("Available bugs for demonstration:")
    for i, bug in enumerate(BUGS, 1):
        print(f"{i}. {bug.name}")
        print(f"   Description: {bug.description}")
        print(f"   Git revision: {bug.git_revision}")
        print()


def get_user_selection() -> Bug:
    """Get user's bug selection."""
    while True:
        try:
            choice = input(f"Select a bug (1-{len(BUGS)}): ").strip()
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
        subprocess.run(["git", "fetch"], check=True)
        
        # Switch to the revision
        subprocess.run(["git", "checkout", revision], check=True)
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
    print("\033[1;37mViv Demo Tool\033[0m")
    print()

    display_bugs()

    # Get user selection
    selected_bug = get_user_selection()
    print(f"Selected: {selected_bug.name}")
    print()

    temp_dir = tempfile.mkdtemp(prefix="viv_demo_")
    artifact_path = os.path.join(temp_dir, "artifacts.tar.gz")

    try:
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