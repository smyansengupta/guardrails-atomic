'use client';

import { Button } from '@/components/ui/button';
import { Clock } from 'lucide-react';
import { Spinner } from '@/components/ui/spinner';

interface GenerateButtonProps {
  onClick: () => void;
  isLoading: boolean;
  canGenerate: boolean;
  remainingSeconds: number;
  disabled?: boolean;
}

/**
 * Button component for generating specs with rate limiting UI
 *
 * Shows different states:
 * - Loading: Shows spinner
 * - Rate limited: Shows countdown timer
 * - Ready: Shows "Generate Spec" text
 *
 * @example
 * <GenerateButton
 *   onClick={handleGenerate}
 *   isLoading={isLoading}
 *   canGenerate={canGenerate}
 *   remainingSeconds={remainingSeconds}
 * />
 */
export function GenerateButton({
  onClick,
  isLoading,
  canGenerate,
  remainingSeconds,
  disabled = false,
}: GenerateButtonProps) {
  const formatTime = (seconds: number): string => {
    if (seconds >= 60) {
      const mins = Math.floor(seconds / 60);
      const secs = seconds % 60;
      return `${mins}:${secs.toString().padStart(2, '0')}`;
    }
    return `${seconds}s`;
  };

  const isDisabled = !canGenerate || isLoading || disabled;

  return (
    <div className="flex flex-col gap-2">
      <Button
        onClick={onClick}
        disabled={isDisabled}
        size="lg"
        className="min-w-[200px]"
      >
        {isLoading ? (
          <>
            <Spinner size="xs" className="mr-2" />
            Generating...
          </>
        ) : !canGenerate ? (
          <>
            <Clock className="mr-2 h-4 w-4" />
            Wait {formatTime(remainingSeconds)}
          </>
        ) : (
          'Generate Specification'
        )}
      </Button>

      {!canGenerate && !isLoading && (
        <p className="text-xs text-muted-foreground text-center">
          Rate limited. You can generate another spec in {formatTime(remainingSeconds)}.
        </p>
      )}
    </div>
  );
}
