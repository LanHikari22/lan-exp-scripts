import os
from pathlib import Path
from unittest import TestCase

TEST_DATA_PATH = Path(os.path.abspath(__file__)).parent / 'test_data'

class Module1UnitTests(TestCase):
    def setUp(self):
        return super().setUp()

    def test_something(self) -> None:
        self.assertTrue(True, "rigorous test :)")
