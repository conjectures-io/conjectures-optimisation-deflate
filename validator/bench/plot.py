#!/usr/bin/env python3
"""Box plots for bench.analyze: ratio and speed by format, colored by method (matplotlib)."""

# matplotlib ships no type information, so the checker sees Any everywhere in here; the two
# functions are small and are exercised on every `just bench-report`.
# pyright: reportAny=false, reportUnknownMemberType=false, reportUnknownVariableType=false, reportUnknownArgumentType=false

from __future__ import annotations

COLORS = {
    "incumbent": "#000000",
    "no-lz77": "#999999",
    "template": "#1f77b4",
    "hc-d4": "#7fb3ff",
    "hc-sparse": "#aec7e8",
    "hash-chains": "#ff7f0e",
    "hc-d64": "#c96a00",
    "lazy": "#2ca02c",
    "mo-lazy": "#8c564b",
    "btree": "#17becf",
    "optimal": "#d62728",
    "libdeflate-12": "#9467bd",
}


def color_for(m: str, fallback_i: int) -> object:
    if m in COLORS:
        return COLORS[m]
    from matplotlib import colormaps

    return colormaps["tab20"](fallback_i % 20)


def boxplot_by_format(
    by_format_method: dict[tuple[str, str], list[float]],
    formats: list[str],
    methods: list[str],
    title: str,
    ylabel: str,
    path: str,
) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(max(8, 1.6 * len(formats)), 5.5))
    n = len(methods)
    width = 0.8 / max(n, 1)
    for mi, method in enumerate(methods):
        positions: list[float] = []
        data: list[list[float]] = []
        for fi, fmt in enumerate(formats):
            vals = by_format_method.get((fmt, method))
            if not vals:
                continue
            positions.append(fi + (mi - (n - 1) / 2) * width)
            data.append(vals)
        if not data:
            continue
        bp = ax.boxplot(
            data, positions=positions, widths=width * 0.9, patch_artist=True, manage_ticks=False
        )
        for box in bp["boxes"]:
            box.set_facecolor(color_for(method, mi))
            box.set_alpha(0.8)
        for med in bp["medians"]:
            med.set_color("black")
    ax.set_xticks(range(len(formats)))
    ax.set_xticklabels(formats, rotation=20, ha="right")
    ax.set_ylabel(ylabel)
    ax.set_title(title)
    ax.grid(True, axis="y", alpha=0.3)
    from matplotlib.patches import Rectangle

    handles = [Rectangle((0, 0), 1, 1, color=color_for(m, i)) for i, m in enumerate(methods)]
    ax.legend(handles, methods, loc="upper left", bbox_to_anchor=(1.01, 1.0), fontsize=8)
    fig.tight_layout()
    fig.savefig(path, dpi=140)
    plt.close(fig)
