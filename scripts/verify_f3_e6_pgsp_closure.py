#!/usr/bin/env python3
"""Exact finite verifier for the six four-space lifts used by the Lean bridge.

Checks, over F3:
  * generated matrix closure has 103680 elements;
  * maximum word distance from identity is 36;
  * the primitive exterior-square kernel is exactly {I,-I};
  * projective quotient order is 51840.

This is a computational regression only.  The Lean owner is authoritative when
its `native_decide` theorems kernel-check.
"""

from collections import deque
import numpy as np

P = 3

LIFTS = [
    np.array([[1,0,1,1],[0,1,1,2],[2,2,2,0],[2,1,0,2]], dtype=np.int8),
    np.array([[2,0,1,1],[0,2,0,1],[1,2,1,0],[0,1,0,1]], dtype=np.int8),
    np.array([[1,0,1,1],[0,1,0,1],[1,2,2,0],[0,1,0,2]], dtype=np.int8),
    np.array([[0,0,2,1],[0,0,2,2],[2,2,0,0],[1,2,0,0]], dtype=np.int8),
    np.array([[0,0,1,1],[0,0,1,0],[0,2,0,0],[2,1,0,0]], dtype=np.int8),
    np.array([[0,0,2,2],[0,0,1,2],[2,1,0,0],[2,2,0,0]], dtype=np.int8),
]

PAIRS = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]


def key(a: np.ndarray) -> bytes:
    return bytes((a % P).astype(np.uint8).ravel())


def exterior6(g: np.ndarray) -> np.ndarray:
    out = np.zeros((6, 6), dtype=np.int8)
    for col, (i, j) in enumerate(PAIRS):
        u, v = g[:, i] % P, g[:, j] % P
        for row, (a, b) in enumerate(PAIRS):
            out[row, col] = (u[a] * v[b] - u[b] * v[a]) % P
    return out % P


def primitive_exterior(g: np.ndarray) -> np.ndarray:
    # q=(p12,p13,p14,p23,p24) expands with p34=-p12.
    expand = np.zeros((6, 5), dtype=np.int8)
    expand[0, 0] = 1
    expand[1, 1] = 1
    expand[2, 2] = 1
    expand[3, 3] = 1
    expand[4, 4] = 1
    expand[5, 0] = 2
    project = np.zeros((5, 6), dtype=np.int8)
    project[:5, :5] = np.eye(5, dtype=np.int8)
    return (project @ exterior6(g) @ expand) % P


def main() -> None:
    identity = np.eye(4, dtype=np.int8)
    seen = {key(identity): identity}
    distance = {key(identity): 0}
    frontier = deque([identity])

    while frontier:
        a = frontier.popleft()
        d = distance[key(a)]
        for g in LIFTS:
            b = (g @ a) % P
            k = key(b)
            if k not in seen:
                seen[k] = b
                distance[k] = d + 1
                frontier.append(b)

    assert len(seen) == 103680, len(seen)
    assert max(distance.values()) == 36, max(distance.values())

    identity5 = np.eye(5, dtype=np.int8) % P
    kernel = [a for a in seen.values() if np.array_equal(primitive_exterior(a), identity5)]
    assert len(kernel) == 2, len(kernel)
    kernel_keys = {key(a) for a in kernel}
    assert kernel_keys == {key(identity), key((-identity) % P)}
    assert len(seen) // len(kernel) == 51840

    print("closure_order=103680")
    print("max_word_distance=36")
    print("exterior_kernel_order=2")
    print("exterior_kernel={+I,-I}")
    print("projective_quotient_order=51840")


if __name__ == "__main__":
    main()
