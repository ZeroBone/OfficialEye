---
icon: material/office-building
---

# Architecture

!!! warning
    This page is in a work-in-progress state and might be incomplete or have many defects.

```mermaid
graph TB
    start_node[Start] -->|Input Image & Templates| unification_phase{{Unification Phase}};
    end_node[End];
    io_driver{{IO Driver}};
    
    unification_phase -- "Unified feature images" --> interpretation_phase{{Interpretation Phase}} -- "Interpretation Result" --> io_driver;
    
    unification_phase & interpretation_phase -. "Errors" .-> io_driver;
    io_driver -- "Output" --> end_node;
```