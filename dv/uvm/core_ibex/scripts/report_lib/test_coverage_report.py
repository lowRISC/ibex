# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from datetime import datetime, timezone
from io import StringIO
from types import SimpleNamespace

import pytest

from report_lib.dvsim_json import create_dvsim_report_dict
from report_lib.html import output_results_html
from report_lib.util import create_cov_summary_dict


@pytest.mark.parametrize('total', [0, 4])
@pytest.mark.parametrize('covergroups', [False, True])
def test_unavailable_coverage(tmp_path, total, covergroups):
    report = tmp_path / 'report'
    report.mkdir()
    (report / 'cov_report.txt').write_text(
        'name block covered\n------------------\n'
        f'ibex_top 0.00%(0/{total})\n')
    group = 'ibex_pkg' if covergroups else 'push_pull_agent_pkg'
    (report / 'cov_report_cg.txt').write_text(
        f'name covergroup average\n------------------\n{group} 50.00%\n')
    metadata = SimpleNamespace(cov_report_log=tmp_path / 'coverage.log',
                               creation_datetime=datetime.now(timezone.utc),
                               git_commit='test')
    summary = create_cov_summary_dict(metadata)
    assert summary['block'] == (0.0 if total else None)
    assert summary['covergroup'] == (0.5 if covergroups else None)
    assert summary['branch'] is None

    tests = {'smoke': {'passing': 1, 'failing': 0}}
    result = create_dvsim_report_dict('xlm', 'ibex', 'test', tests, summary)
    assert result['results']['coverage'] == {
        **({'block': 0.0} if total else {}),
        **({'covergroup': 50.0} if covergroups else {})}
    html = StringIO()
    output_results_html(metadata, [], tests, summary, html)
    assert 'N/A' in html.getvalue()
