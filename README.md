# Red-black tree in Zig

The idea is that all nodes are stored adjacent to each other in
linear memory with the root node always at index 0. This should
allow easy serialization.

## Usage

```zig
// This function should be used to compare nodes
fn comp(lhs: *const u32, rhs: *const u32) Cmp {
    if (lhs.* == rhs.*) {
        return .Equal;
    } else if (lhs.* < rhs.*) {
        return .Smaller;
    } else {
        return .Greater;
    }
}

pub fn main() void {
    const K = u32; // Type of the key
    const V = u32; // Type of the value
    const MAX_NODES = 10; // Tree is fixed to 10 nodes
    
    // Create a new tree type with u32 keys and u32 values 
    const U32Tree = RBTree(K, V, MAX_NODES, comp);
    
    // New tree instance 
    var tree = U32Tree{}; 

    // Insert a element with key = 10 and value = 100
    tree.insert(10, 100);

    // Fetch a node index
    const i = tree.get(10);

    // Get the key of the node at index i
    _ = tree.get_key(i);

    // Get the value of the node at index i
    _ = tree.get_value(i);

    // Delete the node with key = 10
    tree.delete(10);
}
```
