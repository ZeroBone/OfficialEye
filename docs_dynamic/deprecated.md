```mermaid
graph TB
    start_node[Start];
    end_node[End];
    subgraph unification_phase[Unification Phase]
        direction LR
        matching{{Matching}} -- "Matches" --> supervision{{Supervision}};
    end
    subgraph interpretation_phase[Interpretation Phase]
        direction LR
        mutation{{Mutation}} -- "Mutated feature images" --> interpretation{{Interpretation}};
    end
    io_driver{{IO Driver}};
    
    start_node --> unification_phase;
    
    unification_phase -- "Unified feature images" --> interpretation_phase;
    
    interpretation_phase -- "Interpretation Result" --> io_driver;
    
    unification_phase & interpretation_phase -. "Errors" .-> io_driver;
    io_driver -- "Output" --> end_node;
```

# Basic usage

A good introduction to OfficialEye would be to show how to re-create the example of the [home page](index.md). First, we need a high-quality image of an example document. For this tutorial, we shall use the following example of a German identity card:

![Example of an identity card used in Germany](assets/img/identity_card_de.jpg "Example of an identity card used in Germany")

Broadly speaking, we now need to explain OfficialEye, which parts of this example document contain information we are interested in, and which parts are present on any document of this kind and can be used to recognize the document on other images. OfficialEye uses a concept called *template* to conveniently capture in a single unit the example document together with this information. In this case, it makes sense to create a template called `German ID Card` and identifier `id_de`:

```bash
officialeye create demo/templates/id_de.yml --name "German ID Card" --id id_de --force
```

This command creates the configuration file `demo/templates/id_de.yml` for the new template, so that we don't have to configure everything from scratch.

<figure markdown>
  ![Driver license photo](../../assets/img/demo/driver_license_ru_01.jpg){ width="600", loading=lazy }
  <figcaption>Driver's license example photo</figcaption>
</figure>

<div class="grid" markdown>
!!! tip "Template"
    * No further requirements

!!! example "Example document"
    * test
</div>