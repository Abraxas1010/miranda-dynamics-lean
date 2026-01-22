/*
 * Hypergraph Analysis Functions for Wolfram Physics Models
 * Integrates with HeytingLean verified arithmetic
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

/*
 * Hypergraph data structure
 */
typedef struct {
    int64_t* data;          /* Flattened vertex indices */
    int64_t* lengths;       /* Length of each hyperedge */
    int64_t count;          /* Number of hyperedges */
    int64_t total_vertices; /* Total elements in data */
} Hypergraph;

/*
 * Load hypergraph from binary files (exported by Wolfram)
 */
Hypergraph* hypergraph_load(const char* data_path, const char* lengths_path, int64_t count) {
    Hypergraph* hg = (Hypergraph*)malloc(sizeof(Hypergraph));
    if (!hg) return NULL;

    hg->count = count;

    /* Load lengths */
    FILE* f = fopen(lengths_path, "rb");
    if (!f) { free(hg); return NULL; }

    hg->lengths = (int64_t*)malloc(count * sizeof(int64_t));
    if (fread(hg->lengths, sizeof(int64_t), count, f) != (size_t)count) {
        free(hg->lengths); free(hg); fclose(f);
        return NULL;
    }
    fclose(f);

    /* Calculate total vertices */
    hg->total_vertices = 0;
    for (int64_t i = 0; i < count; i++) {
        hg->total_vertices += hg->lengths[i];
    }

    /* Load data */
    f = fopen(data_path, "rb");
    if (!f) { free(hg->lengths); free(hg); return NULL; }

    hg->data = (int64_t*)malloc(hg->total_vertices * sizeof(int64_t));
    if (fread(hg->data, sizeof(int64_t), hg->total_vertices, f) != (size_t)hg->total_vertices) {
        free(hg->data); free(hg->lengths); free(hg); fclose(f);
        return NULL;
    }
    fclose(f);

    return hg;
}

/*
 * Free hypergraph
 */
void hypergraph_free(Hypergraph* hg) {
    if (hg) {
        free(hg->data);
        free(hg->lengths);
        free(hg);
    }
}

/*
 * Get hyperedge by index
 */
int64_t* hypergraph_get_edge(Hypergraph* hg, int64_t index, int64_t* length) {
    if (index < 0 || index >= hg->count) return NULL;

    int64_t offset = 0;
    for (int64_t i = 0; i < index; i++) {
        offset += hg->lengths[i];
    }

    *length = hg->lengths[index];
    return &hg->data[offset];
}

/*
 * Count unique vertices in hypergraph
 */
int64_t hypergraph_vertex_count(Hypergraph* hg) {
    /* Simple O(n^2) implementation - could use hash set for O(n) */
    int64_t max_vertex = 0;
    for (int64_t i = 0; i < hg->total_vertices; i++) {
        if (hg->data[i] > max_vertex) {
            max_vertex = hg->data[i];
        }
    }
    return max_vertex;
}

/*
 * Compute degree distribution
 * Returns array where result[i] = number of vertices with degree i
 */
int64_t* hypergraph_degree_distribution(Hypergraph* hg, int64_t* max_degree) {
    int64_t vertex_count = hypergraph_vertex_count(hg);
    int64_t* degrees = (int64_t*)calloc(vertex_count + 1, sizeof(int64_t));

    /* Count degree of each vertex */
    for (int64_t i = 0; i < hg->total_vertices; i++) {
        if (hg->data[i] <= vertex_count) {
            degrees[hg->data[i]]++;
        }
    }

    /* Find max degree */
    *max_degree = 0;
    for (int64_t i = 0; i <= vertex_count; i++) {
        if (degrees[i] > *max_degree) {
            *max_degree = degrees[i];
        }
    }

    return degrees;
}

/*
 * Compute hyperedge size distribution
 */
int64_t* hypergraph_edge_size_distribution(Hypergraph* hg, int64_t* max_size) {
    *max_size = 0;
    for (int64_t i = 0; i < hg->count; i++) {
        if (hg->lengths[i] > *max_size) {
            *max_size = hg->lengths[i];
        }
    }

    int64_t* distribution = (int64_t*)calloc(*max_size + 1, sizeof(int64_t));
    for (int64_t i = 0; i < hg->count; i++) {
        distribution[hg->lengths[i]]++;
    }

    return distribution;
}

/*
 * Compute total vertex sum (for verification)
 */
int64_t hypergraph_vertex_sum(Hypergraph* hg) {
    int64_t sum = 0;
    for (int64_t i = 0; i < hg->total_vertices; i++) {
        sum += hg->data[i];
    }
    return sum;
}

/*
 * Export functions for Wolfram FFI
 */
int64_t wl_hypergraph_vertex_count(int64_t* data, int64_t total_len) {
    int64_t max_vertex = 0;
    for (int64_t i = 0; i < total_len; i++) {
        if (data[i] > max_vertex) {
            max_vertex = data[i];
        }
    }
    return max_vertex;
}

double wl_hypergraph_density(int64_t* data, int64_t total_len, int64_t edge_count) {
    int64_t vertex_count = wl_hypergraph_vertex_count(data, total_len);
    if (vertex_count == 0) return 0.0;
    /* Density = edges / possible edges */
    return (double)edge_count / (double)(vertex_count * (vertex_count - 1) / 2);
}

int64_t wl_hypergraph_sum(int64_t* data, int64_t total_len) {
    int64_t sum = 0;
    for (int64_t i = 0; i < total_len; i++) {
        sum += data[i];
    }
    return sum;
}

/*
 * Test program
 */
#ifdef HYPERGRAPH_TEST_MAIN
int main(int argc, char* argv[]) {
    if (argc < 4) {
        printf("Usage: %s <data.bin> <lengths.bin> <count>\n", argv[0]);
        return 1;
    }

    int64_t count = atoll(argv[3]);
    Hypergraph* hg = hypergraph_load(argv[1], argv[2], count);

    if (!hg) {
        printf("Failed to load hypergraph\n");
        return 1;
    }

    printf("Hypergraph loaded:\n");
    printf("  Hyperedges: %ld\n", hg->count);
    printf("  Total vertices in edges: %ld\n", hg->total_vertices);
    printf("  Unique vertices: %ld\n", hypergraph_vertex_count(hg));
    printf("  Vertex sum: %ld\n", hypergraph_vertex_sum(hg));

    /* Print first few hyperedges */
    printf("\nFirst 5 hyperedges:\n");
    for (int64_t i = 0; i < 5 && i < hg->count; i++) {
        int64_t len;
        int64_t* edge = hypergraph_get_edge(hg, i, &len);
        printf("  [%ld]: {", i);
        for (int64_t j = 0; j < len; j++) {
            printf("%ld%s", edge[j], j < len-1 ? ", " : "");
        }
        printf("}\n");
    }

    /* Degree distribution */
    int64_t max_degree;
    int64_t* degrees = hypergraph_degree_distribution(hg, &max_degree);
    printf("\nMax vertex degree: %ld\n", max_degree);
    free(degrees);

    /* Edge size distribution */
    int64_t max_size;
    int64_t* sizes = hypergraph_edge_size_distribution(hg, &max_size);
    printf("Edge size distribution:\n");
    for (int64_t i = 1; i <= max_size; i++) {
        if (sizes[i] > 0) {
            printf("  Size %ld: %ld edges\n", i, sizes[i]);
        }
    }
    free(sizes);

    hypergraph_free(hg);
    return 0;
}
#endif
