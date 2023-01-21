import pytest

# Provide smart debug info for assertions that appear in these non-test modules.
# Must appear before module is imported. See:
# https://docs.pytest.org/en/latest/how-to/assert.html#assert-introspection
pytest.register_assert_rewrite("testlib")

import testlib

testlib.install_solidity()
