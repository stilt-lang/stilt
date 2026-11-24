import sys
from collections import defaultdict
from dataclasses import dataclass


@dataclass
class Order:
    """One validated row of the orders file."""

    customer: str
    qty: int
    price: float


def parse_line(n: int, text: str) -> Order:
    """Parses one `customer,qty,price` row."""
    fields = text.split(",")
    if len(fields) != 3:
        raise ValueError(f"line {n}: expected 3 fields")
    customer, q, p = fields
    try:
        qty = int(q)
    except ValueError:
        raise ValueError(f"line {n}: bad qty {q}") from None
    try:
        price = float(p)
    except ValueError:
        raise ValueError(f"line {n}: bad price {p}") from None
    if qty <= 0:
        raise ValueError(f"line {n}: qty must be positive")
    return Order(customer, qty, price)


def totals(orders: list[Order]) -> list[tuple[str, float]]:
    """Revenue per customer, largest first."""
    sums: defaultdict[str, float] = defaultdict(float)
    for o in orders:
        sums[o.customer] += o.qty * o.price
    return sorted(sums.items(), key=lambda kv: kv[1], reverse=True)


def main() -> None:
    try:
        if len(sys.argv) < 2:
            raise ValueError("usage: orders <file>")
        path = sys.argv[1]
        try:
            with open(path) as f:
                lines = f.read().splitlines()
        except OSError:
            raise ValueError(f"cannot read {path}") from None
        orders = [parse_line(n, line) for n, line in enumerate(lines[1:], 2)]
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        sys.exit(1)
    for c, t in totals(orders)[:3]:
        print(f"{c}: {t:.2f}")


main()
