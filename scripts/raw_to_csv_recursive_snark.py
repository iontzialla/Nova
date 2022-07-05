import sys
import os
import csv
import statistics
import numpy as np

def parse_benchmark_name(bench):
    params = bench.split("/");
    assert(len(params) == 2);
    cons_and_step = params[0].split("-");
    num_steps = cons_and_step[-1];
    num_cons = cons_and_step[-3];
    op = params[1];
    return [int(num_cons), num_steps, op]
                    
def parse(fname):
    res = {};
    with open(fname, 'r') as f:
        while True:
            line = f.readline();
            if not line:
                break;
            if "ProofSize" in line:
                entries = line.split(":");
                if len(entries) != 2:
                    print("ERROR: Wrong format of line" + line);
                    sys.exit()
                size = entries[1][:-1].strip().split(" ")[0];
                [num_cons, num_steps, op] = parse_benchmark_name(entries[0]);
                if not op in res: 
                    res[op] = {}; 
                if not num_cons in res[op]:
                    res[op][num_cons] = {};
                # Convert to KB
                res[op][num_cons][int(num_steps)] = float(size)/pow(2,10);
            else:
                entries = list(filter(lambda x: x != "", line.split(" ")));
                if "Benchmarking" in entries:
                    idx = entries.index("Benchmarking");
                    cur_benchmark = entries[idx + 1][:-1];
                if "time:" in entries:
                    idx = entries.index("time:");
                    time = entries[idx + 3]; 
                    time_units = entries[idx + 4];
                    if (cur_benchmark == ""):
                        print("ERROR: Problem while parsing the file, found time without benchmark name");
                        sys.exit();
                    [num_cons, num_steps, op] = parse_benchmark_name(cur_benchmark);
                    if op == "Prove":
                        # Convert to s
                        if time_units == "ms": 
                            time = float(time)/1000;
                        else:
                            assert(time_units == "s");
                    else:
                        # Convert to ms
                        if time_units == "s": 
                            time = float(time)*1000;
                        else:
                            assert(time_units == "ms");
                    if not op in res: 
                        res[op] = {}; 
                    if not num_cons in res[op]:
                        res[op][num_cons] = {};
                    res[op][num_cons][int(num_steps)] = time;
    return res;

def get_medians_per_step(results): 
    res = {};
    for op in results:
        res[op] = [];
        for num_cons in results[op]:
            measurements_per_step = [];
            for num_steps in range(10,30):
                if num_steps not in results[op][num_cons]:
                    break;
                if "Prove" not in op: 
                    measurements_per_step.append(float(results[op][num_cons][num_steps]));
                else: 
                    if num_steps > 3:
                        # Append the difference from the previous step
                        measurements_per_step.append(float(results[op][num_cons][num_steps]) - float(results[op][num_cons][num_steps -1 ]));
            n = np.array(measurements_per_step);
            res[op].append([num_cons, statistics.median(measurements_per_step), np.percentile(n, 5), np.percentile(n, 95)]);
    return res;
            


def write_results_to_csv(results, csv_fname):
    fieldnames = ["Num Constraints", "Median", "5th Percentile", "95th Percentile"]
    with open(csv_fname, mode = "w") as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=fieldnames);
        writer.writeheader();
        while len(results) > 0:
            [num_cons, time, min_time, max_time] =  results.pop();
            writer.writerow({
                "Num Constraints": num_cons,
                "Median": time,
                "5th Percentile": min_time,
                "95th Percentile": max_time,
            });

if __name__ == "__main__":
    # First, parse the results
    results = parse("recursive-snark.txt");
    if not os.path.exists('recursive-snark'):
        os.makedirs('recursive-snark');
    medians_per_step = get_medians_per_step(results);
    write_results_to_csv(medians_per_step["Prove"], "recursive-snark/prove.csv")
    write_results_to_csv(medians_per_step["ProofSize"], "recursive-snark/proof-size.csv")
    write_results_to_csv(medians_per_step["Verify"], "recursive-snark/verify.csv")
