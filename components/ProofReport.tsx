'use client';

import { ProofReport as ProofReportType } from '@/lib/types/verification';
import { Card, CardHeader, CardTitle, CardContent } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { CheckCircle } from 'lucide-react';

interface ProofReportProps {
  report: ProofReportType;
}

export function ProofReport({ report }: ProofReportProps) {
  return (
    <Card className="shadow-lg bg-green-50 border-green-200">
      <CardHeader className="flex flex-row items-center gap-2 text-green-800">
        <CheckCircle className="h-6 w-6" />
        <CardTitle>Verification Complete</CardTitle>
      </CardHeader>
      <CardContent className="space-y-4 text-green-900">
        {report.statesExplored !== undefined && (
          <div>
            <p className="font-semibold">States explored:</p>
            <Badge variant="secondary">{report.statesExplored.toLocaleString()}</Badge>
          </div>
        )}

        {report.constraintsChecked !== undefined && (
          <div>
            <p className="font-semibold">Constraints checked:</p>
            <Badge variant="secondary">{report.constraintsChecked}</Badge>
          </div>
        )}

        <div>
          <p className="font-semibold">Invariants verified:</p>
          <ul className="list-disc list-inside">
            {report.invariantsVerified.map((inv, i) => (
              <li key={i}>{inv}</li>
            ))}
          </ul>
        </div>

        <div>
          <p className="font-semibold">Fault scenarios checked:</p>
          <ul className="list-disc list-inside">
            {report.faultScenariosChecked.map((scenario, i) => (
              <li key={i}>{scenario}</li>
            ))}
          </ul>
        </div>
      </CardContent>
    </Card>
  );
}
