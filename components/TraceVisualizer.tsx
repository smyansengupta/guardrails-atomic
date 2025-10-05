'use client';

import { ExecutionStep } from '@/lib/types/verification';
import { Card, CardHeader, CardTitle, CardContent } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { GitMerge } from 'lucide-react';

interface TraceVisualizerProps {
  trace: ExecutionStep[];
}

export function TraceVisualizer({ trace }: TraceVisualizerProps) {
  return (
    <Card className="shadow-lg bg-white">
      <CardHeader>
        <CardTitle>Counterexample Trace</CardTitle>
      </CardHeader>
      <CardContent>
        <div className="relative pl-6">
          <div className="absolute left-9 top-0 bottom-0 w-0.5 bg-gray-200"></div>
          {trace.map((step, i) => (
            <div key={i} className="relative mb-8">
              <div className="absolute left-0 top-1 transform -translate-x-1/2">
                <div className="w-5 h-5 bg-white border-2 border-gray-300 rounded-full flex items-center justify-center">
                  <GitMerge className="h-3 w-3 text-gray-500" />
                </div>
              </div>
              <Card className="ml-6">
                <CardHeader>
                  <CardTitle className="text-lg">Step {i + 1}: {step.action}</CardTitle>
                </CardHeader>
                <CardContent>
                  <pre className="overflow-x-auto bg-gray-50 p-2 rounded-md font-mono text-sm">
                    <code>{JSON.stringify(step.state, null, 2)}</code>
                  </pre>
                  {step.params && (
                    <div className="mt-2">
                      <p className="font-semibold">Params:</p>
                      <Badge variant="outline">{JSON.stringify(step.params)}</Badge>
                    </div>
                  )}
                </CardContent>
              </Card>
            </div>
          ))}
        </div>
      </CardContent>
    </Card>
  );
}
