Contributing
============

When contributing, please follow the [code style](CODE_STYLE.md) in use.

Pull requests should be a single set of related changes with a clean commit
history free from merge commits.
Each commit should be self-contained, provide a meaningful short summary in
the subject and, if not clear from the subject alone, provide more detail in
the commit description.

Every commit should build with no new regressions introduced, and large commits
should be broken up into multiple distinct commits that take incremental steps
towards the final goal.
For example, large ratification packages should have one commit per individual
extension, with possibly an additional initial commit to add necessary
infrastructure like new types needed for all the subsequent commits.

Unnecessary code churn should be avoided unless as part of a pull request aimed
at improving code quality, such as fixing repeated code style violations or
renaming a function whose meaning is unclear.
Such pull requests should not also introduce significant new functionality.

It is desirable in a pull request to explain how the code presented
has been verified and how the verification has been made
reproducible. Ideally the pull request is accompanied by some form of
automated verification that is presented in a way that the reviewers
of the pull request can run. It is desirable that the pull request
explains how it relates to the existing RISC-V architectural tests.

We recommend installing pre-commit hooks that ensure certain basic coding
style issues can be detected and fixed before submitting the pull request.
To set up these hooks, install [https://pre-commit.com/](pre-commit)
(e.g. using `pip install --user pre-commit`) and run `pre-commit install`.
