# Kotzig–Ringel–Rosa (KRR) Conjecture Formalization in Lean 4

This project aims to provide a complete formalization of the proof of the **Kotzig–Ringel–Rosa (KRR) Conjecture** (also known as the **Graceful Tree Conjecture**) as presented in the paper [*"A proof of the Kotzig–Ringel–Rosa Conjecture"*](https://arxiv.org/abs/2202.03178) by Edinah K. Gnang.

The conjecture states that every tree has a graceful labeling. This project formalizes the mathematical foundations, the functional reformulation of the labeling problem, and the verification of the labeling construction described in the proof.

## Project Structure

The formalization is organized into several modules:

*   [`KRR/Basic.lean`](file:///c:/Math/KRR/KRR/Basic.lean): Basic definitions of trees, graph structures, and labeling functions.
*   [`KRR/FunctionalReformulation.lean`](file:///c:/Math/KRR/KRR/FunctionalReformulation.lean): Mapping the graceful labeling problem into a functional/algebraic framework as described in the paper.
*   [`KRR/Graceful.lean`](file:///c:/Math/KRR/KRR/Graceful.lean): The core proof logic and verification of the graceful property for tree labelings.
*   [`KRR.lean`](file:///c:/Math/KRR/KRR.lean): Main entry point and theorem statements.

## Current Status

- [x] Initial project structure and mathlib integration.
- [ ] Formal definitions of tree graceful labeling.
- [ ] Implementation of the functional mapping from the Gnang proof.
- [ ] Verification of the main labeling construction.

## Getting Started

### Prerequisites

1.  **Lean 4**: Ensure you have Lean 4 installed. The recommended way is via `elan`.
    ```powershell
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    ```
2.  **Visual Studio Code**: Use VS Code with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) for the best development experience.

### Building the Project

To build the project and compile the Lean files:

```powershell
lake build
```

### Running Tests

If there are any tests or examples to run:

```powershell
lake exe krr
```

## Contributing

Contributions are welcome! If you find any issues or want to help complete the formalization:
1. Fork the repository.
2. Create a new branch for your feature or bugfix.
3. Submit a pull request.

## License

This project is licensed under the Apache License 2.0. See the [LICENSE](LICENSE) file for details.
