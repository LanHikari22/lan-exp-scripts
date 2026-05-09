from typing import List, Dict, Tuple, Union
from dataclasses import dataclass
import matplotlib.pyplot as plt
import checkpipe as pipe
import numpy as np
import enum


class PlotLinePattern(enum.Enum):
    SCATTER = enum.auto()
    LINE = enum.auto()
    SCATTER_AND_LINE = enum.auto()

@dataclass
class PlotLineSettings:
    pattern: PlotLinePattern
    label_x: str
    label_y: str
    title: str

@dataclass
class XYFloatColumnLists:
    xs: List[float]
    ys: List[float]

    @staticmethod
    def from_list_of_tup(l: List[Tuple[Union[int, float], Union[int, float]]], reverse=False) -> 'XYFloatColumnLists':
        columns = XYFloatColumnLists._get_columns(l)

        if reverse:
            return XYFloatColumnLists(columns[1], columns[0])
        else:
            return XYFloatColumnLists(columns[0], columns[1])
    
    @staticmethod
    def _get_columns(l: List[Tuple[Union[int, float], Union[int, float]]]) -> Tuple[List[float], List[float]]:
        def get_column(n: int) -> List[float]:
            return (
                l
                    .__iter__()
                    | pipe.OfIter[Tuple[Union[int, float], Union[int, float]]].map(lambda x_y: float(x_y[n]))
                    | pipe.OfIter[float].to_list()
            )

        x_column = get_column(0)
        y_column = get_column(1)

        return (x_column, y_column)

    def scatterplot_and_display(self, settings: PlotLineSettings):
        _, ax = plt.subplots()

        if settings.pattern == PlotLinePattern.SCATTER:
            ax.scatter(self.xs, self.ys)
        elif settings.pattern == PlotLinePattern.LINE:
            ax.plot(self.xs, self.ys)
        elif settings.pattern == PlotLinePattern.SCATTER_AND_LINE:
            ax.scatter(self.xs, self.ys)
            ax.plot(self.xs, self.ys)
        else:
            raise Exception("Invalid PlotLinePattern")

        ax.set(xlabel=settings.label_x, ylabel=settings.label_y, title=settings.title)
        ax.grid()
        plt.show()